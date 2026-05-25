use serde::Deserialize;
use tla_connect::*;

// ── Hanoi application ─────────────────────────────────────────────

/// Tower of Hanoi — 3 pegs with disks stacked largest-to-smallest.
///
/// Each peg is a `Vec<i64>` stored bottom-to-top (index 0 = bottom).
/// Disk numbers are 1 (smallest) through N (largest).
#[derive(Debug, Clone, PartialEq)]
pub struct Hanoi {
    pegs: [Vec<i64>; 3],
}

impl Hanoi {
    /// Initialise from explicit peg states (bottom-to-top).
    pub fn init(a: Vec<i64>, b: Vec<i64>, c: Vec<i64>) -> Self {
        Self { pegs: [a, b, c] }
    }

    /// Move the top disk from one peg to another.
    ///
    /// Returns `Err` if the move is illegal (empty source or disk
    /// larger than destination's top).
    pub fn move_disk(&mut self, from: &str, to: &str) -> Result<(), String> {
        let src = peg_index(from)?;
        let dst = peg_index(to)?;

        let disk = self.pegs[src]
            .last()
            .copied()
            .ok_or_else(|| format!("peg {from} is empty"))?;

        if let Some(&top) = self.pegs[dst].last() {
            if disk > top {
                return Err(format!(
                    "disk {disk} too large for peg {to} (top is {top})"
                ));
            }
        }

        self.pegs[src].pop();
        self.pegs[dst].push(disk);
        Ok(())
    }
}

fn peg_index(name: &str) -> Result<usize, String> {
    match name {
        "A" => Ok(0),
        "B" => Ok(1),
        "C" => Ok(2),
        other => Err(format!("unknown peg: {other}")),
    }
}

// ── tla-connect bridge ────────────────────────────────────────────

/// Extract a peg's disk stack from an ITF List value
/// (TLA+ sequences are encoded as JSON arrays → `itf::Value::List`).
fn extract_peg(val: &itf::Value) -> Vec<i64> {
    if let itf::Value::List(disks) = val {
        disks
            .iter()
            .map(|d| {
                if let itf::Value::BigInt(n) = d {
                    n.to_string().parse().unwrap_or(0)
                } else {
                    0
                }
            })
            .collect()
    } else {
        vec![]
    }
}

/// Read the `from` and `to` fields from the nondet_picks record.
fn extract_move_picks(nondet: &itf::Value) -> (String, String) {
    let (mut from, mut to) = (String::new(), String::new());
    if let itf::Value::Record(rec) = nondet {
        if let Some(itf::Value::String(s)) = rec.get("from") {
            from = s.clone();
        }
        if let Some(itf::Value::String(s)) = rec.get("to") {
            to = s.clone();
        }
    }
    (from, to)
}

/// Snapshot of [`Hanoi`] state for comparison with the TLA+ spec.
#[derive(Debug, PartialEq, Deserialize)]
struct HanoiState {
    #[serde(rename = "A")]
    a: Vec<i64>,
    #[serde(rename = "B")]
    b: Vec<i64>,
    #[serde(rename = "C")]
    c: Vec<i64>,
}

impl State<HanoiDriver> for HanoiState {
    fn from_driver(driver: &HanoiDriver) -> Result<Self, DriverError> {
        Ok(HanoiState {
            a: driver.hanoi.pegs[0].clone(),
            b: driver.hanoi.pegs[1].clone(),
            c: driver.hanoi.pegs[2].clone(),
        })
    }
}

/// Thin adapter that injects [`Hanoi`] into the tla-connect
/// `Driver` trait so it can be driven by ITF trace replay.
struct HanoiDriver {
    hanoi: Hanoi,
}

impl Default for HanoiDriver {
    fn default() -> Self {
        Self {
            hanoi: Hanoi::init(vec![], vec![], vec![]),
        }
    }
}

impl Driver for HanoiDriver {
    type State = HanoiState;

    fn step(&mut self, step: &Step) -> Result<(), DriverError> {
        switch!(step {
            "init" => {
                if let itf::Value::Record(state) = &step.state {
                    let a = state.get("A").map(extract_peg).unwrap_or_default();
                    let b = state.get("B").map(extract_peg).unwrap_or_default();
                    let c = state.get("C").map(extract_peg).unwrap_or_default();
                    self.hanoi = Hanoi::init(a, b, c);
                }
            },
            "move" => {
                let (from, to) = extract_move_picks(&step.nondet_picks);
                self.hanoi.move_disk(&from, &to).map_err(|e| {
                    DriverError::ActionFailed {
                        action: "move".into(),
                        reason: e,
                    }
                })?;
            },
        })
    }
}

// ── main ──────────────────────────────────────────────────────────

fn main() -> Result<(), Error> {
    let config = ApalacheConfig::builder()
        .spec("spec/Hanoi.tla")
        .inv("TraceComplete")
        .cinit("HanoiConstInit")
        .max_traces(5)
        .max_length(30)
        .mode(ApalacheMode::Simulate)
        .build();

    println!("Generating traces from TLA+ spec...");
    let generated = generate_traces(&config)?;
    let total_states: usize = generated.traces.iter().map(|t| t.states.len()).sum();
    println!(
        "Generated {} traces with {} total states",
        generated.traces.len(),
        total_states,
    );

    println!("Replaying traces against HanoiDriver...");
    replay_traces(HanoiDriver::default, &generated.traces)?;
    println!("All traces replayed successfully!");

    Ok(())
}
