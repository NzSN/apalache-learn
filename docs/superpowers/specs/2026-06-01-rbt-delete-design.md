# RBT.tla Deterministic Delete Operation

## Context

`examples/RB-Tree/RBT.tla` currently specifies a deterministic Red-Black Tree **Insert** operation with bounded/unrolled helpers suitable for Apalache model checking. It lacks a Delete operation. The Rust counterpart (`rb_tree.rs`) also only implements Insert.

## Design

### Approach

Unrolled/bounded style, following the existing Insert patterns exactly:
- Depth-limited BST traversal (depth ≤ 3)
- Bounded fixup iterations (5 max)
- 3-pass BH recomputation
- `CHOOSE` for deterministic choices from sets

### New Helpers

| Helper | Signature | Purpose |
|--------|-----------|---------|
| `BSTFind` | `(n, r, key) => Int` | Bounded BST lookup returning node ID for `key` or `nil` |
| `Successor` | `(n, id) => Int` | In-order successor (min of right subtree), bounded depth |
| `ChildOf` | `(n, id) => Int` | The sole non-nil child of `id`, or `nil` if 0 or 2 children |
| `DeleteFixIt` | `(n, r, x) => {n, r, x, done}` | Single iteration of delete fixup (cases: sibling red, sibling black with black children, sibling black with red wedge, sibling black with red line) |
| `DeleteFixup` | `(n, r, x) => {n, r, x, done}` | Bounded fixup, 5 iterations unrolled (like `Fixup`) |
| `Transplant` | `(n, r, u, v) => {n, r}` | Replace subtree at `u` with `v`, updating parent link |

### Delete(key) Operator

```tla
Delete(key) ==
    IF key \notin TreeKeys
    THEN UNCHANGED (no-op, like Insert)
    ELSE
        LET z == BSTFind(nodes, root, key)
            n0 == IF nodes[z].left /= nil /\ nodes[z].right /= nil
                  THEN LET y == Successor(nodes, z)
                       IN [nodes EXCEPT ![z].key = nodes[y].key]  \* key moved to z
                  ELSE nodes
            delId == IF n0 = nodes THEN z ELSE Successor(nodes, z)
            x == ChildOf(n0, delId)
            transRes == Transplant(n0, root, delId, x)
            delColor == nodes[delId].color
            fixRes == IF delColor = "B"
                      THEN DeleteFixup(transRes.n, transRes.r, x)
                      ELSE transRes
            n1 == [fixRes.n EXCEPT ![fixRes.r].color = "B"]
            finalNodes == RecomputeBH(n1)
        IN /\ nodes' = finalNodes
           /\ root' = fixRes.r
           /\ Inv'
           /\ action_taken' = "delete"
           /\ step_count' = step_count + 1
```

### Next Relation Update

```tla
Next ==
    \/ \E key \in KEYS: Insert(key)
    \/ \E key \in TreeKeys: Delete(key)
    \/ UNCHANGED <<nodes, root, action_taken, step_count>>
```

### Delete Fixup Cases

For a node `x` (double-black), with sibling `w`:

1. **Sibling red**: Recolor sibling black, parent red, rotate parent toward x, update sibling
2. **Sibling black, both children black**: Recolor sibling red, bubble up to parent
3. **Sibling black, red wedge child**: Recolor wedge black, sibling red, rotate sibling away from x, update sibling
4. **Sibling black, red line child**: Recolor sibling = parent color, parent black, line child black, rotate parent toward x, done

### Bounds

- `BSTFind` / `Successor`: depth ≤ 3
- `DeleteFixup`: maximum 5 iterations
- BH recomputation: 3 passes
- `MAX_NODES = 5`, `KEYS = {1,2,3,4,5}` — tree depth at most 5

### Invariants

All existing invariants (`NilInv`, `RootBlack`, `NoDoubleRed`, `BSTInv`, `BHInv`) must hold after delete.
`TraceComplete == step_count < 3` may need adjustment for insert+delete scenarios.
