use std::path::PathBuf;
use tla_connect as T;

pub struct ApalacheMBT {
    spec: PathBuf,
    max_traces: u32,
    max_length: u32,
    invariant: String,
    mode: T::ApalacheMode,
    cinit: Option<String>,
    view: Option<String>,
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
            view: None,
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

    pub fn view(mut self, view: impl Into<String>) -> Self {
        self.view = Some(view.into());
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

        if let Some(ref view) = self.view {
            builder = builder.view(view);
        }

        builder.build().expect("T::ApalacheConfig build should always succeed")
    }
}

pub struct InteractiveMBT {
    spec: PathBuf,
    init: String,
    next: String,
    max_steps: usize,
    num_runs: usize,
    seed: Option<u64>,
    server_url: String,
    constants: serde_json::Value,
}

impl InteractiveMBT {
    pub fn new(spec: impl Into<PathBuf>) -> Self {
        Self {
            spec: spec.into(),
            init: "Init".into(),
            next: "Next".into(),
            max_steps: 10,
            num_runs: 10,
            seed: None,
            server_url: "http://localhost:8822".into(),
            constants: serde_json::Value::Object(serde_json::Map::new()),
        }
    }

    pub fn init(mut self, init: impl Into<String>) -> Self {
        self.init = init.into();
        self
    }

    pub fn next(mut self, next: impl Into<String>) -> Self {
        self.next = next.into();
        self
    }

    pub fn max_steps(mut self, n: usize) -> Self {
        self.max_steps = n;
        self
    }

    pub fn num_runs(mut self, n: usize) -> Self {
        self.num_runs = n;
        self
    }

    pub fn seed(mut self, seed: u64) -> Self {
        self.seed = Some(seed);
        self
    }

    pub fn server_url(mut self, url: impl Into<String>) -> Self {
        self.server_url = url.into();
        self
    }

    pub fn constants(mut self, constants: serde_json::Value) -> Self {
        self.constants = constants;
        self
    }

    pub fn run<D: T::Driver>(&self, driver_fn: impl Fn() -> D + Send) -> Result<(), T::Error> {
        let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
        rt.block_on(async {
            let client = T::ApalacheRpcClient::new(&self.server_url)?;

            let mut builder = T::InteractiveConfig::builder()
                .spec(self.spec.clone())
                .init(&self.init)
                .next(&self.next)
                .max_steps(self.max_steps)
                .num_runs(self.num_runs);

            if !self.constants.is_null()
                && self
                    .constants
                    .as_object()
                    .is_none_or(|m| m.is_empty())
                == false
            {
                builder = builder.constants(self.constants.clone());
            }

            if let Some(seed) = self.seed {
                builder = builder.seed(seed);
            }

            let config = builder.build().expect("InteractiveConfig build should always succeed");

            println!(
                "Running {} interactive test runs (max {} steps each)...",
                config.num_runs,
                config.max_steps,
            );

            let stats = T::interactive_test(driver_fn, &client, &config).await?;

            println!(
                "Completed {} runs, {} total steps, {} deadlocks in {:?}",
                stats.runs_completed,
                stats.total_steps,
                stats.deadlocks_hit,
                stats.duration,
            );

            Ok(())
        })
    }
}
