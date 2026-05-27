use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};
use std::hash::{Hash, Hasher};
use serde::Deserialize;

// ── SimpleKVCache application ────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Entry {
    pub val: i64,
    pub ts: i64,
}

impl PartialOrd for Entry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Entry {
    fn cmp(&self, other: &Self) -> Ordering {
        self.ts.cmp(&other.ts).then_with(|| self.val.cmp(&other.val))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Request {
    pub key: i64,
    pub ts: i64,
}

impl PartialOrd for Request {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Request {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key).then_with(|| self.ts.cmp(&other.ts))
    }
}

impl Hash for Request {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key.hash(state);
        self.ts.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
pub struct Write {
    pub key: i64,
    pub val: i64,
    pub ts: i64,
}

pub struct SimpleKVCache {
    pub now: i64,
    pub store: BTreeMap<i64, Entry>,
    pub cache: BTreeMap<i64, Entry>,
    pub requests: HashSet<Request>,
    pub replies: BTreeMap<Request, Entry>,
    pub writes_history: Vec<Write>,
    delta: i64,
    ttl: i64,
}

impl SimpleKVCache {
    pub fn new(delta: i64) -> Self {
        Self {
            now: 0,
            store: BTreeMap::new(),
            cache: BTreeMap::new(),
            requests: HashSet::new(),
            replies: BTreeMap::new(),
            writes_history: Vec::new(),
            delta,
            ttl: 2 * delta,
        }
    }

    pub fn put(&mut self, key: i64, val: i64) {
        self.store.insert(key, Entry { val, ts: self.now });
        self.writes_history.push(Write { key, val, ts: self.now });
    }

    pub fn get_ok(&mut self, key: i64) -> Result<(), String> {
        let entry = self
            .cache
            .get(&key)
            .ok_or_else(|| format!("GetOk: key {key} not in cache"))?;
        if self.now >= entry.ts + self.ttl {
            return Err(format!(
                "GetOk: key {key} TTL expired (now={}, entry.ts={}, TTL={})",
                self.now, entry.ts, self.ttl
            ));
        }
        Ok(())
    }

    pub fn get_miss(&mut self, key: i64) -> Result<(), String> {
        if let Some(entry) = self.cache.get(&key) {
            if self.now <= entry.ts + self.ttl {
                return Err(format!("GetMiss: key {key} still valid in cache"));
            }
        }
        self.requests.insert(Request { key, ts: self.now });
        self.cache.remove(&key);
        Ok(())
    }

    pub fn send_reply(&mut self, req_key: i64, req_ts: i64) -> Result<(), String> {
        let req = Request { key: req_key, ts: req_ts };
        if !self.requests.contains(&req) {
            return Err(format!("SendReply: req ({req_key},{req_ts}) not in requests"));
        }
        if self.replies.contains_key(&req) {
            return Err(format!("SendReply: req ({req_key},{req_ts}) already replied"));
        }
        if self.now > req_ts + self.delta {
            return Err(format!(
                "SendReply: req ({req_key},{req_ts}) too old (now={}, delta={})",
                self.now, self.delta
            ));
        }
        let entry = self
            .store
            .get(&req_key)
            .ok_or_else(|| format!("SendReply: key {req_key} not in store"))?;
        self.replies
            .insert(req.clone(), Entry { val: entry.val, ts: self.now });
        Ok(())
    }

    pub fn recv_reply(&mut self, req_key: i64, req_ts: i64) -> Result<(), String> {
        let req = Request { key: req_key, ts: req_ts };
        let reply = self
            .replies
            .get(&req)
            .ok_or_else(|| format!("RecvReply: req ({req_key},{req_ts}) not in replies"))?;
        if self.now > reply.ts + self.delta {
            return Err(format!("RecvReply: reply for ({req_key},{req_ts}) too old"));
        }
        self.cache
            .insert(req_key, Entry { val: reply.val, ts: self.now });
        Ok(())
    }

    pub fn set_now(&mut self, ts: i64) -> Result<(), String> {
        if ts <= self.now {
            return Err(format!("set_now: ts {ts} must be > now {}", self.now));
        }
        self.now = ts;
        Ok(())
    }
}

#[cfg(not(test))]
fn main() {
    eprintln!("Run MBT verification via: cargo test --example simple_kv_cache");
}

#[cfg(test)]
mod tests {
    use tla_connect as T;
    use super::*;
    use apalache_learn::model_check::ApalacheMBT;

    // ── State for comparison ──────────────────────────────────────────

    #[derive(Debug, PartialEq, Eq, Deserialize)]
    struct CacheState {
        now: i64,
        store: Vec<(i64, Entry)>,
        cache: Vec<(i64, Entry)>,
        requests: Vec<Request>,
        replies: Vec<(Request, Entry)>,
        writes_history: Vec<Write>,
    }

    impl T::State for CacheState {
        fn from_spec(value: &itf::Value) -> Result<Self, T::DriverError> {
            let rec = expect_record(value)?;
            Ok(CacheState {
                now: extract_int(rec, "now")?,
                store: sorted_kv_map(extract_field(rec, "store")?)?,
                cache: sorted_kv_map(extract_field(rec, "cache")?)?,
                requests: sorted_set(extract_field(rec, "requests")?)?,
                replies: sorted_req_kv_map(extract_field(rec, "replies")?)?,
                writes_history: extract_seq(rec, "writes_history")?,
            })
        }
    }

    impl T::ExtractState<CacheDriver> for CacheState {
        fn from_driver(driver: &CacheDriver) -> Result<Self, T::DriverError> {
            let kvc = &driver.kvc;
            Ok(CacheState {
                now: kvc.now,
                store: kvc.store.iter().map(|(k, v)| (*k, v.clone())).collect(),
                cache: kvc.cache.iter().map(|(k, v)| (*k, v.clone())).collect(),
                requests: {
                    let mut v: Vec<_> = kvc.requests.iter().cloned().collect();
                    v.sort();
                    v
                },
                replies: {
                    let mut v: Vec<_> = kvc
                        .replies
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();
                    v.sort();
                    v
                },
                writes_history: kvc.writes_history.clone(),
            })
        }
    }

    // ── Driver ────────────────────────────────────────────────────────

    struct CacheDriver {
        kvc: SimpleKVCache,
    }

    impl Default for CacheDriver {
        fn default() -> Self {
            Self {
                kvc: SimpleKVCache::new(5),
            }
        }
    }

    impl T::Driver for CacheDriver {
        type State = CacheState;

        fn step(&mut self, step: &T::Step) -> Result<(), T::DriverError> {
            let action_err = |action: &str, e: String| T::DriverError::ActionFailed {
                action: action.into(),
                reason: e,
            };

            if step.action_taken == "init" {
                self.kvc = SimpleKVCache::new(5);
                return Ok(());
            }

            match step.action_taken.as_str() {
                "Put" => {
                    let (key, val) = extract_picks_kv(&step.nondet_picks)?;
                    self.kvc.put(key, val);
                },
                "GetOk" => {
                    let key = extract_picks_key(&step.nondet_picks)?;
                    self.kvc.get_ok(key).map_err(|e| action_err("GetOk", e))?;
                },
                "GetMiss" => {
                    let key = extract_picks_key(&step.nondet_picks)?;
                    self.kvc.get_miss(key).map_err(|e| action_err("GetMiss", e))?;
                },
                "SendReply" => {
                    let (req_key, req_ts) = extract_picks_req(&step.nondet_picks)?;
                    self.kvc.send_reply(req_key, req_ts).map_err(|e| action_err("SendReply", e))?;
                },
                "RecvReply" => {
                    let (req_key, req_ts) = extract_picks_req(&step.nondet_picks)?;
                    self.kvc.recv_reply(req_key, req_ts).map_err(|e| action_err("RecvReply", e))?;
                },
                other => return Err(T::DriverError::UnknownAction(other.to_string())),
            }

            let rec = expect_record(&step.state)?;
            self.kvc.now = extract_int(rec, "now")?;
            Ok(())
        }
    }

    // ── ITF extraction helpers ────────────────────────────────────────

    fn state_err(msg: impl Into<String>) -> T::DriverError {
        T::DriverError::StateExtraction(msg.into())
    }

    fn expect_record(v: &itf::Value) -> Result<&itf::value::Record, T::DriverError> {
        match v {
            itf::Value::Record(r) => Ok(r),
            other => Err(state_err(format!("expected Record, got {other:?}"))),
        }
    }

    fn extract_field<'a>(
        rec: &'a itf::value::Record,
        field: &str,
    ) -> Result<&'a itf::Value, T::DriverError> {
        rec.get(field)
            .ok_or_else(|| state_err(format!("missing field {field}")))
    }

    fn extract_int(rec: &itf::value::Record, field: &str) -> Result<i64, T::DriverError> {
        let v = extract_field(rec, field)?;
        match v {
            itf::Value::BigInt(n) => n.to_string().parse().map_err(|e| state_err(format!("{field}: {e}"))),
            itf::Value::Number(n) => Ok(*n),
            other => Err(state_err(format!("{field}: expected int, got {other:?}"))),
        }
    }

    fn to_i64(v: &itf::Value) -> Result<i64, T::DriverError> {
        match v {
            itf::Value::BigInt(n) => n.to_string().parse().map_err(|e| state_err(format!("BigInt: {e}"))),
            itf::Value::Number(n) => Ok(*n),
            other => Err(state_err(format!("expected int, got {other:?}"))),
        }
    }

    fn extract_entry(val: &itf::Value) -> Result<Entry, T::DriverError> {
        Entry::deserialize(val.clone()).map_err(|e| state_err(format!("Entry: {e}")))
    }

    fn extract_seq(
        rec: &itf::value::Record,
        field: &str,
    ) -> Result<Vec<Write>, T::DriverError> {
        let v = extract_field(rec, field)?;
        Vec::<Write>::deserialize(v.clone()).map_err(|e| state_err(format!("writes_history: {e}")))
    }

    fn sorted_kv_map(v: &itf::Value) -> Result<Vec<(i64, Entry)>, T::DriverError> {
        match v {
            itf::Value::Map(map) => {
                let mut result = Vec::new();
                for (key, val) in map.iter() {
                    let k = to_i64(key)?;
                    let v = extract_entry(val)?;
                    result.push((k, v));
                }
                result.sort_by(|a, b| a.0.cmp(&b.0));
                Ok(result)
            }
            other => Err(state_err(format!("expected Map, got {other:?}"))),
        }
    }

    fn sorted_set(v: &itf::Value) -> Result<Vec<Request>, T::DriverError> {
        match v {
            itf::Value::Set(set) => {
                let mut result = Vec::new();
                for elem in set.iter() {
                    let req = Request::deserialize(elem.clone())
                        .map_err(|e| state_err(format!("Request: {e}")))?;
                    result.push(req);
                }
                result.sort();
                Ok(result)
            }
            other => Err(state_err(format!("expected Set, got {other:?}"))),
        }
    }

    fn sorted_req_kv_map(v: &itf::Value) -> Result<Vec<(Request, Entry)>, T::DriverError> {
        match v {
            itf::Value::Map(map) => {
                let mut result = Vec::new();
                for (key, val) in map.iter() {
                    let req = Request::deserialize(key.clone())
                        .map_err(|e| state_err(format!("Request key: {e}")))?;
                    let entry = extract_entry(val)?;
                    result.push((req, entry));
                }
                result.sort();
                Ok(result)
            }
            other => Err(state_err(format!("expected Map, got {other:?}"))),
        }
    }

    fn extract_picks_kv(v: &itf::Value) -> Result<(i64, i64), T::DriverError> {
        let rec = expect_record(v)?;
        Ok((extract_int(rec, "key")?, extract_int(rec, "val")?))
    }

    fn extract_picks_key(v: &itf::Value) -> Result<i64, T::DriverError> {
        let rec = expect_record(v)?;
        extract_int(rec, "key")
    }

    fn extract_picks_req(v: &itf::Value) -> Result<(i64, i64), T::DriverError> {
        let rec = expect_record(v)?;
        Ok((extract_int(rec, "req_key")?, extract_int(rec, "req_ts")?))
    }

    // ── Test ──────────────────────────────────────────────────────────

    #[test]
    fn mbt_verify() -> Result<(), T::Error> {
        let mbt = ApalacheMBT::new("examples/SimpleKVCache/spec/MC_mbt.tla")
            .max_traces(5)
            .max_length(30)
            .invariant("TraceComplete,Inv1,Inv2,Inv3,Inv4");

        mbt.run(CacheDriver::default)
    }
}
