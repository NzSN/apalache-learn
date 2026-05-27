use std::path::PathBuf;
use tla_connect as T;

pub struct ApalacheMBT {
    spec: PathBuf,
    max_traces: u32,
    max_length: u32,
    invariant: String,
    mode: T::ApalacheMode,
    cinit: Option<String>,
}

impl ApalacheMBT {
    pub fn new(spec: impl Into<PathBuf>) -> Self {
        Self {
            spec: spec.into(),
            max_traces: 100,
            max_length: 50,
            invariant: "TraceComplete".into(),
            mode: T::ApalacheMode::Simulate,
            cinit: None,
        }
    }

    pub fn max_traces(mut self, n: u32) -> Self {
        self.max_traces = n;
        self
    }

    pub fn max_length(mut self, n: u32) -> Self {
        self.max_length = n;
        self
    }

    pub fn invariant(mut self, inv: impl Into<String>) -> Self {
        self.invariant = inv.into();
        self
    }

    pub fn mode(mut self, mode: T::ApalacheMode) -> Self {
        self.mode = mode;
        self
    }

    pub fn cinit(mut self, cinit: impl Into<String>) -> Self {
        self.cinit = Some(cinit.into());
        self
    }

    pub fn run<D: T::Driver>(&self, driver_fn: impl Fn() -> D) -> Result<(), T::Error> {
        let config = self.to_config();
        let generated = T::generate_traces(&config)?;
        let total_states: usize = generated.traces.iter().map(|t| t.states.len()).sum();

        println!(
            "Generated {} traces with {} total states",
            generated.traces.len(),
            total_states,
        );

        println!("Replaying traces...");
        let _stats = T::replay_traces(driver_fn, &generated.traces)?;
        println!("All traces replayed successfully!");

        Ok(())
    }

    fn to_config(&self) -> T::ApalacheConfig {
        let mut builder = T::ApalacheConfig::builder()
            .spec(self.spec.clone())
            .inv(&self.invariant)
            .max_traces(self.max_traces as usize)
            .max_length(self.max_length as usize)
            .mode(self.mode);

        if let Some(ref cinit) = self.cinit {
            builder = builder.cinit(cinit);
        }

        builder.build().expect("T::ApalacheConfig build should always succeed")
    }
}
