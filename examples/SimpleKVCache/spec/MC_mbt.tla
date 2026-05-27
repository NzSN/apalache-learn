----------------------------------- MODULE MC_mbt -----------------------------------
EXTENDS Integers, Sequences, FiniteSets

KEYS == 0..(2^32 - 1)
VALUES == 0..(2^32 - 1)
TIMESTAMPS == 0..(24 * 60 * 60)
DELTA == 5
TTL == 2 * DELTA

VARIABLES
    \* @type: Int;
    now,
    \* @type: Int -> { val: Int, ts: Int };
    store,
    \* @type: Int -> { val: Int, ts: Int };
    cache,
    \* @type: Set({ key: Int, ts: Int });
    requests,
    \* @type: { key: Int, ts: Int } -> { val: Int, ts: Int };
    replies,
    \* @type: Seq({ key: Int, val: Int, ts: Int });
    writes_history,
    \* @type: Str;
    action_taken,
    \* @type: { key: Int, val: Int, req_key: Int, req_ts: Int };
    nondet_picks,
    \* @type: Int;
    step_count

Init ==
    /\ now = 0
    /\ store = [k \in {} |-> [val |-> 0, ts |-> 0]]
    /\ cache = [k \in {} |-> [val |-> 0, ts |-> 0]]
    /\ requests = {}
    /\ replies = [k \in {} |-> [val |-> 0, ts |-> 0]]
    /\ writes_history = <<>>
    /\ action_taken = "init"
    /\ nondet_picks = [key |-> 0, val |-> 0, req_key |-> 0, req_ts |-> 0]
    /\ step_count = 0

Put(key, val) ==
    /\ key \in KEYS
    /\ val \in VALUES
    /\ action_taken' = "Put"
    /\ store' = [k \in DOMAIN store \union {key} |->
            IF k = key THEN [val |-> val, ts |-> now] ELSE store[k]]
    /\ writes_history' = Append(writes_history, [key |-> key, val |-> val, ts |-> now])
    /\ nondet_picks' = [key |-> key, val |-> val, req_key |-> 0, req_ts |-> 0]
    /\ UNCHANGED <<cache, requests, replies>>

GetOk(key) ==
    /\ key \in KEYS
    /\ action_taken' = "GetOk"
    /\ key \in DOMAIN cache
    /\ LET entry == cache[key] IN
       /\ now < entry.ts + TTL
    /\ nondet_picks' = [key |-> key, val |-> 0, req_key |-> 0, req_ts |-> 0]
    /\ UNCHANGED <<store, cache, requests, replies, writes_history>>

GetMiss(key) ==
    /\ key \in KEYS
    /\ action_taken' = "GetMiss"
    /\ key \in DOMAIN cache => (now > cache[key].ts + TTL)
    /\ requests' = requests \union {[key |-> key, ts |-> now]}
    /\ cache' = [k \in DOMAIN cache \ {key} |-> cache[k]]
    /\ nondet_picks' = [key |-> key, val |-> 0, req_key |-> 0, req_ts |-> 0]
    /\ UNCHANGED <<store, replies, writes_history>>

SendReply(req_key, req_ts) ==
    /\ req_key \in KEYS
    /\ req_ts \in TIMESTAMPS
    /\ action_taken' = "SendReply"
    /\ LET req == [key |-> req_key, ts |-> req_ts] IN
       /\ req \in requests
       /\ req \notin DOMAIN replies
       /\ req_key \in DOMAIN store
       /\ now <= req_ts + DELTA
       /\ LET entry == store[req_key] IN
           /\ replies' = [k \in DOMAIN replies \union {req} |->
                IF k = req THEN [val |-> entry.val, ts |-> now] ELSE replies[k]]
    /\ nondet_picks' = [key |-> 0, val |-> 0, req_key |-> req_key, req_ts |-> req_ts]
    /\ UNCHANGED <<store, cache, requests, writes_history>>

RecvReply(req_key, req_ts) ==
    /\ req_key \in KEYS
    /\ req_ts \in TIMESTAMPS
    /\ action_taken' = "RecvReply"
    /\ LET req == [key |-> req_key, ts |-> req_ts] IN
       /\ req \in DOMAIN replies
       /\ LET reply == replies[req] IN
           /\ now <= reply.ts + DELTA
           /\ cache' = [k \in DOMAIN cache \union {req_key} |->
                IF k = req_key THEN [val |-> reply.val, ts |-> now] ELSE cache[k]]
    /\ nondet_picks' = [key |-> 0, val |-> 0, req_key |-> req_key, req_ts |-> req_ts]
    /\ UNCHANGED <<store, requests, replies, writes_history>>

Next ==
    /\ \E ts \in TIMESTAMPS:
        ts > now /\ now' = ts
    /\ step_count' = step_count + 1
    /\ \/ \E key \in KEYS, val \in VALUES: Put(key, val)
       \/ \E key \in KEYS: GetOk(key)
       \/ \E key \in KEYS: GetMiss(key)
       \/ \E req_key \in KEYS, req_ts \in TIMESTAMPS: SendReply(req_key, req_ts)
       \/ \E req_key \in KEYS, req_ts \in TIMESTAMPS: RecvReply(req_key, req_ts)

TraceComplete == step_count < 10

Inv1 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key]
               store_entry == store[key] IN
           (cache_entry.ts >= store_entry.ts) => cache_entry.val = store_entry.val

Inv2 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key] IN
           \E i \in DOMAIN writes_history:
               LET write == writes_history[i] IN
               /\ write.key = key
               /\ write.val = cache_entry.val
               /\ write.ts <= cache_entry.ts

Inv3 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key] IN
           \E i \in DOMAIN writes_history:
               LET write == writes_history[i] IN
               /\ write.key = key
               /\ write.val = cache_entry.val
               /\ write.ts <= cache_entry.ts
               /\ \A j \in DOMAIN writes_history:
                    LET other_write == writes_history[j] IN
                    \/ other_write.key /= key
                    \/ other_write.val = write.val
                    \/ other_write.ts >= cache_entry.ts
                    \/ other_write.ts < write.ts

Inv4 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key] IN
           \E i \in DOMAIN writes_history:
               LET write == writes_history[i] IN
               /\ write.key = key
               /\ write.val = cache_entry.val
               /\ write.ts <= cache_entry.ts
               /\ \A j \in DOMAIN writes_history:
                    LET other_write == writes_history[j] IN
                    \/ other_write.key /= key
                    \/ other_write.val = write.val
                    \/ other_write.ts \notin (write.ts + 1)..(cache_entry.ts - TTL)
===================================================================================
