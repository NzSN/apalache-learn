// ── HourClock application ─────────────────────────────────────────────

pub struct HourClock {
    hr: i64,
    latest_hr: i64,
    ticked: bool,
}

impl HourClock {
    pub fn init(start_hr: i64, start_latest_hr: i64) -> Result<Self, String> {
        if !(1..=12).contains(&start_hr) {
            return Err(format!("start_hr {start_hr} out of range 1..12"));
        }
        if !(1..=12).contains(&start_latest_hr) {
            return Err(format!("start_latest_hr {start_latest_hr} out of range 1..12"));
        }
        Ok(Self {
            hr: start_hr,
            latest_hr: start_latest_hr,
            ticked: false,
        })
    }

    pub fn tick(&mut self) -> Result<(), String> {
        self.ticked = true;
        self.latest_hr = self.hr;
        self.hr = if self.hr == 12 { 1 } else { self.hr + 1 };
        Ok(())
    }
}

#[cfg(not(test))]
fn main() {
    eprintln!("Run MBT verification via: cargo test --example hourclock");
}

#[cfg(test)]
mod tests {
    use tla_connect as T;
    use tla_connect::switch;
    use serde::Deserialize;

    use super::HourClock;
    use apalache_learn::model_check::ApalacheMBT;

    fn extract_init_picks(nondet: &itf::Value) -> (i64, i64) {
        let mut start_hr = 0i64;
        let mut start_latest_hr = 0i64;
        if let itf::Value::Record(rec) = nondet {
            if let Some(itf::Value::BigInt(n)) = rec.get("start_hr") {
                start_hr = n.to_string().parse().unwrap_or(0);
            }
            if let Some(itf::Value::BigInt(n)) = rec.get("start_latest_hr") {
                start_latest_hr = n.to_string().parse().unwrap_or(0);
            }
        }
        (start_hr, start_latest_hr)
    }

    #[derive(Debug, PartialEq, Deserialize)]
    struct HourClockState {
        hr: i64,
        latest_hr: i64,
        ticked: bool,
    }

    impl T::State for HourClockState {}

    impl T::ExtractState<HourClockDriver> for HourClockState {
        fn from_driver(driver: &HourClockDriver) -> Result<Self, T::DriverError> {
            Ok(HourClockState {
                hr: driver.clock.hr,
                latest_hr: driver.clock.latest_hr,
                ticked: driver.clock.ticked,
            })
        }
    }

    struct HourClockDriver {
        clock: HourClock,
    }

    impl Default for HourClockDriver {
        fn default() -> Self {
            Self {
                clock: HourClock::init(1, 1).unwrap(),
            }
        }
    }

    impl T::Driver for HourClockDriver {
        type State = HourClockState;

        fn step(&mut self, step: &T::Step) -> Result<(), T::DriverError> {
            switch!(step {
                "init" => {
                    let (start_hr, start_latest_hr) = extract_init_picks(&step.nondet_picks);
                    self.clock = HourClock::init(start_hr, start_latest_hr)
                        .map_err(|e| T::DriverError::ActionFailed {
                            action: "init".into(),
                            reason: e,
                        })?;
                    Ok(())
                },
                "tick" => {
                    self.clock.tick().map_err(|e| T::DriverError::ActionFailed {
                        action: "tick".into(),
                        reason: e,
                    })?;
                    Ok(())
                },
            })
        }
    }

    #[test]
    fn mbt_verify() -> Result<(), T::Error> {
        let mbt = ApalacheMBT::new("examples/HourClock/HourClock.tla")
            .max_traces(5)
            .max_length(13)
            .invariant("TraceComplete");
        mbt.run(HourClockDriver::default)
    }
}
