# RBT.tla: TLA+ Specification of a Red-Black Tree (Insert-Only)

## Problem

Before implementing a Red-Black (RB) tree in Rust, we need a formal TLA+
specification to serve as a reference for model-based testing. The spec must
define the RB invariants and model the insertion operation so Apalache can
verify that inserted keys always produce a valid tree.

## Goal

A TLA+ module `RBT.tla` under `examples/RB-Tree/` that:

- Defines what constitutes a valid RB tree (root black, no red-red, BST, equal
  black height)
- Models an atomic insert operation that adds a key and produces a tree
  satisfying all invariants
- Is checkable by Apalache with bounded model checking
- Follows existing conventions (Apalache type annotations, `Init`/`Next`/`Inv`)

## Design

### Representation

The tree is stored as a total function `nodes: Int -> NodeRecord` on a fixed
set of node IDs `0..MAX_NODES` (ID 0 is the NIL sentinel). Each record has
fields `key`, `color`, `left`, `right`, and `bh` (black height). Unused nodes
have `key = 0` and point to NIL. The `root` variable tracks the root node ID.

A `bh` field in each node is maintained so black-height equality can be
checked structurally (constant-time per node) without recursive traversal.

### RB Invariants (`Inv`)

1. **Nil invariant** — the NIL node always has the canonical NilRec value
2. **Root black** — root is either NIL or black
3. **No double red** — no red node has a red child
4. **BST** — for each node, left key < node key < right key
5. **Black height** — siblings have equal `bh`; a node's `bh` is its
   children's `bh` plus 1 if black

### Operations

- **`Init`** — empty tree: `nodes` maps all IDs to empty records, `root = nil`
- **`Insert(key)`** — atomic: if key already exists, no change; otherwise
  nondeterministically chooses `nodes'` and `root'` such that `Inv'` holds and
  `TreeKeys' = TreeKeys \union {key}`
- **`Next`** — `\E key \in KEYS: Insert(key)` or stuttering
- **`TraceComplete`** — `step_count < 3` for bounded checking

### Apalache integration

- Constants `KEYS` (set of possible keys) and `MAX_NODES` (max tree size)
- `ConstInit` pins `KEYS = {1,2,3,4,5}` and `MAX_NODES = 5`
- Type annotations on all variables
- Check command: `apalache-mc check --cinit=ConstInit --inv=Inv --length=3 RBT.tla`

## Verification result

```
State 0: state invariant 0-5 hold
State 1: state invariant 0-5 hold
State 2: state invariant 0-5 hold
State 3: state invariant 0-5 hold
The outcome is: NoError
```

All RB invariants hold across 3 insertion steps.

## Spec self-review

- No placeholders, TODOs, or incomplete sections
- Architecture is consistent: operators reference `nodes`/`root` directly; `Inv'` is used in `Insert` to verify the next state
- Scope is focused: insert-only, atomic operation, bounded model checking
- No ambiguous requirements

## Next steps

- Implement the RB tree in Rust following this spec
- Wire up model-based testing via `tla_connect` + `ApalacheMBT`
