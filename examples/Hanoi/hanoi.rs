// ── Hanoi application ─────────────────────────────────────────────

pub struct Hanoi {
    pegs: [Vec<i64>; 3],
}

impl Hanoi {
    pub fn init_disks(disks: i64) -> Self {
        let a: Vec<i64> = (1..=disks).rev().collect();
        Self {
            pegs: [a, vec![], vec![]],
        }
    }

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

#[cfg(not(test))]
fn main() {
    eprintln!("Run MBT verification via: cargo test --example hanoi");
}

#[cfg(test)]
mod tests {
    use tla_connect as T;
    use tla_connect::switch;
    use serde::Deserialize;

    use super::Hanoi;
    use apalache_learn::model_check::ApalacheMBT;

    fn extract_move_picks(nondet: &itf::Value) -> (String, String) {
        let mut from = String::new();
        let mut to = String::new();
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

    #[derive(Debug, PartialEq, Deserialize)]
    struct HanoiState {
        #[serde(rename = "A")]
        a: Vec<i64>,
        #[serde(rename = "B")]
        b: Vec<i64>,
        #[serde(rename = "C")]
        c: Vec<i64>,
    }

    impl T::State for HanoiState {}

    impl T::ExtractState<HanoiDriver> for HanoiState {
        fn from_driver(driver: &HanoiDriver) -> Result<Self, T::DriverError> {
            Ok(HanoiState {
                a: driver.hanoi.pegs[0].clone(),
                b: driver.hanoi.pegs[1].clone(),
                c: driver.hanoi.pegs[2].clone(),
            })
        }
    }

    struct HanoiDriver {
        hanoi: Hanoi,
    }

    impl Default for HanoiDriver {
        fn default() -> Self {
            Self {
                hanoi: Hanoi::init_disks(3),
            }
        }
    }

    impl T::Driver for HanoiDriver {
        type State = HanoiState;

        fn step(&mut self, step: &T::Step) -> Result<(), T::DriverError> {
            switch!(step {
                "init" => {
                    self.hanoi = Hanoi::init_disks(3);
                    Ok(())
                },
                "move" => {
                    let (from, to) = extract_move_picks(&step.nondet_picks);
                    self.hanoi.move_disk(&from, &to).map_err(|e| {
                        T::DriverError::ActionFailed {
                            action: "move".into(),
                            reason: e,
                        }
                    })?;
                    Ok(())
                },
            })
        }
    }

    #[test]
    fn mbt_verify() -> Result<(), T::Error> {
        let mbt = ApalacheMBT::new("examples/Hanoi/Hanoi.tla")
            .max_traces(5)
            .max_length(15)
            .cinit("HanoiConstInit")
            .invariant("TraceComplete");

        mbt.run(HanoiDriver::default)
    }
}
