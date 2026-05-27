# ActionRegistry Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Create a reusable `ActionRegistry<D, S>` that decouples TLA+ action dispatch from the implementation data, then migrate both examples to use it.

**Architecture:** A new shared crate `tla-registry` under `examples/` exports `ActionRegistry<D, S>`. It holds the implementation data, a `HashMap<String, ActionHandler>` for runtime dispatch, and implements the `Driver` trait. Both `HourClock` and `Hanoi` examples depend on it via path dependency and replace their ad-hoc `XxxDriver` structs with factory functions.

**Tech Stack:** Rust, tla-connect 0.0.2, serde, itf

---

### Task 1: Create tla-registry shared crate

**Files:**
- Create: `examples/tla-registry/Cargo.toml`
- Create: `examples/tla-registry/src/lib.rs`

- [ ] **Step 1: Create Cargo.toml**

```toml
[package]
name = "tla-registry"
version = "0.1.0"
edition = "2021"

[dependencies]
tla-connect = "0.0.2"
```

- [ ] **Step 2: Write lib.rs — ActionRegistry type, constructor, register, Driver impl**

Create `examples/tla-registry/src/lib.rs`:

```rust
use std::collections::HashMap;
use std::marker::PhantomData;
use tla_connect::{Driver, DriverError, State, Step};

pub type ActionHandler<D> = Box<dyn Fn(&mut D, &Step) -> Result<(), DriverError>>;

pub struct ActionRegistry<D, S> {
    pub data: D,
    actions: HashMap<String, ActionHandler<D>>,
    _state: PhantomData<S>,
}

impl<D, S> ActionRegistry<D, S> {
    pub fn new(data: D) -> Self {
        Self {
            data,
            actions: HashMap::new(),
            _state: PhantomData,
        }
    }

    pub fn register(
        &mut self,
        action: impl Into<String>,
        handler: impl Fn(&mut D, &Step) -> Result<(), DriverError> + 'static,
    ) -> &mut Self {
        self.actions.insert(action.into(), Box::new(handler));
        self
    }
}

impl<D: 'static, S: State<ActionRegistry<D, S>> + 'static> Driver for ActionRegistry<D, S> {
    type State = S;

    fn step(&mut self, step: &Step) -> Result<(), DriverError> {
        match self.actions.get(&step.action_taken) {
            Some(handler) => handler(&mut self.data, step),
            None => Err(DriverError::UnknownAction(step.action_taken.clone())),
        }
    }
}
```

- [ ] **Step 3: Build tla-registry to verify it compiles**

```bash
cargo build
```

Expected: `cargo build` succeeds with no errors.

- [ ] **Step 4: Commit**

```bash
git add examples/tla-registry/ && git commit -m "Add tla-registry shared crate with ActionRegistry<D, S>"
```

---

### Task 2: Migrate HourClock to ActionRegistry

**Files:**
- Modify: `examples/HourClock/Cargo.toml`
- Modify: `examples/HourClock/src/main.rs`

- [ ] **Step 1: Add tla-registry dependency to Cargo.toml**

Replace the contents of `examples/HourClock/Cargo.toml`:

```toml
[package]
name = "HourClock"
version = "0.1.0"
edition = "2024"

[dependencies]
tla-connect = "0.0.2"
tla-registry = { path = "../tla-registry" }
serde = { version = "1", features = ["derive"] }
itf = "0.4"
```

- [ ] **Step 2: Rewrite main.rs to use ActionRegistry instead of HourClockDriver**

Replace the contents of `examples/HourClock/src/main.rs`:

```rust
use serde::Deserialize;
use tla_connect::*;
use tla_registry::ActionRegistry;

// ── HourClock application ──────────────────────────────────────────

/// A 12-hour clock that ticks forward.
#[derive(Debug, Clone, PartialEq)]
pub struct HourClock {
    pub hr: i64,
    pub latest_hr: i64,
    pub ticked: bool,
}

impl HourClock {
    /// Initialise the clock with chosen starting values.
    pub fn init(start_hr: i64, start_latest_hr: i64) -> Self {
        Self {
            hr: start_hr,
            latest_hr: start_latest_hr,
            ticked: false,
        }
    }

    /// Advance the clock by one hour. Wraps from 12 back to 1.
    pub fn tick(&mut self) {
        self.latest_hr = self.hr;
        self.hr = if self.hr != 12 { self.hr + 1 } else { 2 };
        self.ticked = true;
    }
}

impl Default for HourClock {
    fn default() -> Self {
        Self::init(0, 0)
    }
}

// ── helpers ────────────────────────────────────────────────────────

/// Read the nondeterministic picks that Apalache chose during `HCinit`.
fn extract_nondet_picks(nondet: &itf::Value) -> (i64, i64) {
    let (mut start_hr, mut start_latest_hr) = (0, 0);
    if let itf::Value::Record(rec) = nondet {
        if let Some(itf::Value::BigInt(val)) = rec.get("start_hr") {
            start_hr = val.to_string().parse().unwrap_or(0);
        }
        if let Some(itf::Value::BigInt(val)) = rec.get("start_latest_hr") {
            start_latest_hr = val.to_string().parse().unwrap_or(0);
        }
    }
    (start_hr, start_latest_hr)
}

// ── State ──────────────────────────────────────────────────────────

/// Snapshot of [`HourClock`] state for comparison with the TLA+ spec.
#[derive(Debug, PartialEq, Deserialize)]
struct HourClockState {
    hr: i64,
    latest_hr: i64,
    ticked: bool,
}

impl State<ActionRegistry<HourClock, HourClockState>> for HourClockState {
    fn from_driver(
        driver: &ActionRegistry<HourClock, HourClockState>,
    ) -> Result<Self, DriverError> {
        Ok(HourClockState {
            hr: driver.data.hr,
            latest_hr: driver.data.latest_hr,
            ticked: driver.data.ticked,
        })
    }
}

// ── registry factory ───────────────────────────────────────────────

fn make_driver() -> ActionRegistry<HourClock, HourClockState> {
    let mut r = ActionRegistry::new(HourClock::default());
    r.register("init", |data, step| {
        let (start_hr, start_latest_hr) = extract_nondet_picks(&step.nondet_picks);
        *data = HourClock::init(start_hr, start_latest_hr);
        Ok(())
    });
    r.register("tick", |data, _step| {
        data.tick();
        Ok(())
    });
    r
}

// ── main ───────────────────────────────────────────────────────────

fn main() -> Result<(), Error> {
    let config = ApalacheConfig::builder()
        .spec("spec/HourClock.tla")
        .inv("TraceComplete")
        .max_traces(10)
        .max_length(20)
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

    println!("Replaying traces against HourClockDriver...");
    replay_traces(make_driver, &generated.traces)?;
    println!("All traces replayed successfully!");

    Ok(())
}
```

- [ ] **Step 3: Build and test**

```bash
cargo build
```

Expected: `cargo build` succeeds with no errors.

- [ ] **Step 4: Run the HourClock example to verify it still works**

```bash
cargo run
```

Expected: Output shows "Generated X traces" then "All traces replayed successfully!"

- [ ] **Step 5: Commit**

```bash
git add examples/HourClock/ && git commit -m "Migrate HourClock to ActionRegistry"
```

---

### Task 3: Migrate Hanoi to ActionRegistry

**Files:**
- Modify: `examples/Hanoi/Cargo.toml`
- Modify: `examples/Hanoi/src/main.rs`

- [ ] **Step 1: Add tla-registry dependency to Cargo.toml**

Replace the contents of `examples/Hanoi/Cargo.toml`:

```toml
[package]
name = "Hanoi"
version = "0.1.0"
edition = "2021"

[dependencies]
tla-connect = "0.0.2"
tla-registry = { path = "../tla-registry" }
serde = { version = "1", features = ["derive"] }
itf = "0.4"
```

- [ ] **Step 2: Rewrite main.rs to use ActionRegistry instead of HanoiDriver**

Replace the contents of `examples/Hanoi/src/main.rs`:

```rust
use serde::Deserialize;
use tla_connect::*;
use tla_registry::ActionRegistry;

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

impl Default for Hanoi {
    fn default() -> Self {
        Self::init(vec![], vec![], vec![])
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

// ── helpers ────────────────────────────────────────────────────────

/// Extract a peg's disk stack from an ITF List value.
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

// ── State ──────────────────────────────────────────────────────────

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

impl State<ActionRegistry<Hanoi, HanoiState>> for HanoiState {
    fn from_driver(
        driver: &ActionRegistry<Hanoi, HanoiState>,
    ) -> Result<Self, DriverError> {
        Ok(HanoiState {
            a: driver.data.pegs[0].clone(),
            b: driver.data.pegs[1].clone(),
            c: driver.data.pegs[2].clone(),
        })
    }
}

// ── registry factory ───────────────────────────────────────────────

fn make_driver() -> ActionRegistry<Hanoi, HanoiState> {
    let mut r = ActionRegistry::new(Hanoi::default());
    r.register("init", |data, step| {
        if let itf::Value::Record(state) = &step.state {
            let a = state.get("A").map(extract_peg).unwrap_or_default();
            let b = state.get("B").map(extract_peg).unwrap_or_default();
            let c = state.get("C").map(extract_peg).unwrap_or_default();
            *data = Hanoi::init(a, b, c);
        }
        Ok(())
    });
    r.register("move", |data, step| {
        let (from, to) = extract_move_picks(&step.nondet_picks);
        data.move_disk(&from, &to).map_err(|e| {
            DriverError::ActionFailed {
                action: "move".into(),
                reason: e,
            }
        })
    });
    r
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
    replay_traces(make_driver, &generated.traces)?;
    println!("All traces replayed successfully!");

    Ok(())
}
```

- [ ] **Step 3: Build and test**

```bash
cargo build
```

Expected: `cargo build` succeeds with no errors.

- [ ] **Step 4: Commit**

```bash
git add examples/Hanoi/ && git commit -m "Migrate Hanoi to ActionRegistry"
```

---

### Task 4: Verification — run both examples

- [ ] **Step 1: Run HourClock**

```bash
cargo run
```

Workdir: `examples/HourClock`

Expected: Output shows "Generated X traces" then "All traces replayed successfully!"

- [ ] **Step 2: Run Hanoi**

```bash
cargo run
```

Workdir: `examples/Hanoi`

Expected: Output shows "Generated X traces" then "All traces replayed successfully!"

- [ ] **Step 3: Commit final verification**

```bash
git add . && git commit -m "Verify both examples work with ActionRegistry"
```
