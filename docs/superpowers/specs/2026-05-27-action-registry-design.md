# ActionRegistry: Decouple Spec-Action Dispatch from Driver

## Problem

Currently, every TLA+ spec requires a hand-written `Driver` implementation that
hardcodes the mapping from TLA+ action names to Rust method calls inside a
`switch!` macro.  The `HourClockDriver` and `HanoiDriver` in the examples
both repeat this pattern:

```rust
impl Driver for HourClockDriver {
    fn step(&mut self, step: &Step) -> Result<(), DriverError> {
        switch!(step {
            "init" => { self.clock = HourClock::init(...); },
            "tick" => { self.clock.tick(); },
        })
    }
}
```

The driver is coupled to the specific implementation type and its methods.
There is no reusable infrastructure — each new spec requires a fresh
`Driver` impl from scratch.

## Goal

A generic, reusable `ActionRegistry` that:

- Owns the implementation data (`D`)
- Registers action handlers at runtime via a builder API
- Dispatches TLA+ actions by name to the corresponding handler
- Implements `Driver` so it can be passed directly to `replay_traces`

The user writes a factory function instead of a `Driver` impl.  No
`switch!` macro needed.

## Design

### New types (`tla_connect::registry` module)

```rust
pub struct ActionRegistry<D, S> {
    /// The implementation data under test.  Public so `State::from_driver`
    /// can inspect it when extracting comparable state.
    pub data: D,
    actions: HashMap<String, ActionHandler<D>>,
    _state: PhantomData<S>,
}

pub type ActionHandler<D> = Box<dyn Fn(&mut D, &Step) -> Result<(), DriverError>>;
```

### Builder API (mutable, returns `&mut Self`)

```rust
impl<D: 'static, S: 'static> ActionRegistry<D, S> {
    pub fn new(data: D) -> Self { ... }

    pub fn register(
        &mut self,
        action: impl Into<String>,
        handler: impl Fn(&mut D, &Step) -> Result<(), DriverError> + 'static,
    ) -> &mut Self { ... }
}
```

### Driver trait implementation

```rust
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

### State extraction

The user still implements `State<ActionRegistry<D, S>>` for their state
type `S`, accessing `driver.data` to extract the comparable fields:

```rust
impl State<ActionRegistry<HourClock, HourClockState>> for HourClockState {
    fn from_driver(driver: &ActionRegistry<HourClock, HourClockState>) -> Result<Self, DriverError> {
        Ok(HourClockState {
            hr: driver.data.hr,
            latest_hr: driver.data.latest_hr,
            ticked: driver.data.ticked,
        })
    }
}
```

`State::from_spec` keeps its default serde-based deserialization from ITF
— no change needed.

### User workflow

Instead of writing a `Driver` impl, the user writes a factory function:

```rust
fn make_driver() -> impl Driver<State = HourClockState> {
    let mut r = ActionRegistry::new(HourClock::default());
    r.register("init", |data, step| {
        let (hr, lat) = extract_nondet_picks(&step.nondet_picks);
        *data = HourClock::init(hr, lat);
        Ok(())
    });
    r.register("tick", |data, _step| {
        data.tick();
        Ok(())
    });
    r
}

fn main() -> Result<(), Error> {
    let traces = generate_traces(&config)?;
    replay_traces(make_driver, &traces.traces)?;
    Ok(())
}
```

### Changes to tla-connect

- New `pub mod registry` module with `ActionRegistry`, `ActionHandler`.
- No changes to existing traits (`Driver`, `State`, `Step`) or modules.

### Changes to examples

- `HourClock/src/main.rs`: Replace `HourClockDriver` with `make_driver()`.
- `Hanoi/src/main.rs`: Replace `HanoiDriver` with `make_driver()`.

## Non-goals

- No proc macros or derive macros in this iteration.
- No automatic action-to-method inference by naming convention.
- No integration with the RPC or trace-validation approaches (scope is
  replay-only).
