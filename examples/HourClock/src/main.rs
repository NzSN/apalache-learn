use serde::Deserialize;
use tla_connect::*;

// ── HourClock application ──────────────────────────────────────────

/// A 12-hour clock that ticks forward.
///
/// This is the real application — it can be used standalone in
/// production code without any dependency on tla-connect.
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

// ── tla-connect bridge ─────────────────────────────────────────────

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

/// Snapshot of [`HourClock`] state for comparison with the TLA+ spec.
#[derive(Debug, PartialEq, Deserialize)]
struct HourClockState {
    hr: i64,
    latest_hr: i64,
    ticked: bool,
}

impl State<HourClockDriver> for HourClockState {
    fn from_driver(driver: &HourClockDriver) -> Result<Self, DriverError> {
        Ok(HourClockState {
            hr: driver.clock.hr,
            latest_hr: driver.clock.latest_hr,
            ticked: driver.clock.ticked,
        })
    }
}

/// Thin adapter that injects [`HourClock`] into the tla-connect
/// `Driver` trait so it can be driven by ITF trace replay.
struct HourClockDriver {
    clock: HourClock,
}

impl Default for HourClockDriver {
    fn default() -> Self {
        Self {
            clock: HourClock::init(0, 0),
        }
    }
}

impl Driver for HourClockDriver {
    type State = HourClockState;

    fn step(&mut self, step: &Step) -> Result<(), DriverError> {
        switch!(step {
            "init" => {
                let (start_hr, start_latest_hr) =
                    extract_nondet_picks(&step.nondet_picks);
                self.clock = HourClock::init(start_hr, start_latest_hr);
            },
            "tick" => {
                self.clock.tick();
            },
        })
    }
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
    replay_traces(HourClockDriver::default, &generated.traces)?;
    println!("All traces replayed successfully!");

    Ok(())
}
