# RB-Tree Deterministic Delete Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a deterministic RB-tree Delete operation to `examples/RB-Tree/RBT.tla`, matching the bounded/unrolled style of the existing Insert.

**Architecture:** Add 5 new bounded helpers (BSTFind, Successor, DeleteFixIt, DeleteFixup) and a Delete(key) operator. DeleteFixIt uses parent hints `(px, xLeft)` to handle the `x=nil` edge case (Pof cannot find nil's parent). After one fixup iteration, `x` is always a real node and Pof works. The Next relation adds `\E key \in TreeKeys: Delete(key)`.

**Tech Stack:** TLA+ with Apalache type annotations

---

### Task 1: Add BSTFind helper

**Files:**
- Modify: `examples/RB-Tree/RBT.tla` — insert after `BSTParent` (line 83)

- [ ] **Step 1: Add BSTFind operator**

Insert after `BSTParent` (after line 83, before `RotLeft` comment):

```tla
\* BST lookup for a key (unrolled, depth ≤ 3). Returns node ID or nil.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int) => Int;
BSTFind(n, r, key) ==
    IF r = nil THEN nil
    ELSE IF n[r].key = key THEN r
    ELSE LET c == IF key < n[r].key THEN n[r].left ELSE n[r].right
         IN IF c = nil THEN nil
            ELSE IF n[c].key = key THEN c
            ELSE LET c2 == IF key < n[c].key THEN n[c].left ELSE n[c].right
                 IN IF c2 = nil THEN nil
                    ELSE IF n[c2].key = key THEN c2
                    ELSE nil
```

- [ ] **Step 2: Commit**

```bash
git add examples/RB-Tree/RBT.tla
git commit -m "feat: add BSTFind operator for delete"
```

---

### Task 2: Add Successor helper

**Files:**
- Modify: `examples/RB-Tree/RBT.tla` — insert after `BSTFind`

- [ ] **Step 1: Add Successor operator**

Insert after `BSTFind`:

```tla
\* In-order successor of id (min of right subtree). Bounded depth ≤ 3.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int) => Int;
Successor(n, id) ==
    LET r == n[id].right
    IN IF r = nil THEN nil
       ELSE IF n[r].left = nil THEN r
       ELSE IF n[n[r].left].left = nil THEN n[r].left
       ELSE n[n[r].left].left
```

- [ ] **Step 2: Commit**

```bash
git add examples/RB-Tree/RBT.tla
git commit -m "feat: add Successor operator for delete"
```

---

### Task 3: Add DeleteFixIt, DeleteFixup helpers

**Files:**
- Modify: `examples/RB-Tree/RBT.tla` — insert after `RecomputeBH` (after line 178, before `Init` comment)

- [ ] **Step 1: Add DeleteFixIt operator**

Insert after `RecomputeBH` (after line 178), before `Init`:

```tla
\* Single delete-fixup iteration. (px, xLeft) are parent hints for the nil case;
\* pass (nil, FALSE) when x is a real node (Pof is used instead).
\* Returns { n, r, x, px, xLeft, done }.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int, Int, Bool) => { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int, x: Int, px: Int, xLeft: Bool, done: Bool };
DeleteFixIt(n, r, x, px, xLeft) ==
    LET par == IF px /= nil THEN px ELSE Pof(n, r, x)
        isLeft == IF px /= nil THEN xLeft ELSE (par /= nil /\ n[par].left = x)
    IN IF x = r \/ (x /= nil /\ n[x].color = "R")
       THEN [n |-> n, r |-> r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
       ELSE IF par = nil
            THEN [n |-> n, r |-> r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
            ELSE LET w == IF isLeft THEN n[par].right ELSE n[par].left
                     wRed == w /= nil /\ n[w].color = "R"
                 IN IF wRed
                    THEN LET n1 == [n EXCEPT ![w].color = "B",
                                               ![par].color = "R"]
                             rot == IF isLeft
                                    THEN RotLeft(n1, r, par)
                                    ELSE RotRight(n1, r, par)
                         IN [n |-> rot.n, r |-> rot.r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> FALSE]
                    ELSE LET wL == n[w].left
                             wR == n[w].right
                             wLB == wL = nil \/ n[wL].color = "B"
                             wRB == wR = nil \/ n[wR].color = "B"
                         IN IF wLB /\ wRB
                            THEN [n |-> [n EXCEPT ![w].color = "R"],
                                   r |-> r, x |-> par, px |-> nil, xLeft |-> FALSE, done |-> FALSE]
                            ELSE IF isLeft
                                 THEN IF wR /= nil /\ n[wR].color = "R"
                                      THEN LET n1 == [n EXCEPT ![w].color = n[par].color,
                                                                 ![par].color = "B",
                                                                 ![wR].color = "B"]
                                               rot == RotLeft(n1, r, par)
                                           IN [n |-> rot.n, r |-> rot.r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
                                      ELSE LET nearC == wL
                                               n1 == [n EXCEPT ![nearC].color = "B",
                                                                  ![w].color = "R"]
                                               rot1 == RotRight(n1, r, w)
                                               w2 == rot1.n[par].right
                                               w2R == rot1.n[w2].right
                                               n2 == [rot1.n EXCEPT ![w2].color = rot1.n[par].color,
                                                                       ![par].color = "B",
                                                                       ![w2R].color = "B"]
                                               rot2 == RotLeft(n2, rot1.r, par)
                                           IN [n |-> rot2.n, r |-> rot2.r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
                                 ELSE IF wL /= nil /\ n[wL].color = "R"
                                      THEN LET n1 == [n EXCEPT ![w].color = n[par].color,
                                                                 ![par].color = "B",
                                                                 ![wL].color = "B"]
                                               rot == RotRight(n1, r, par)
                                           IN [n |-> rot.n, r |-> rot.r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
                                      ELSE LET nearC == wR
                                               n1 == [n EXCEPT ![nearC].color = "B",
                                                                  ![w].color = "R"]
                                               rot1 == RotLeft(n1, r, w)
                                               w2 == rot1.n[par].left
                                               w2L == rot1.n[w2].left
                                               n2 == [rot1.n EXCEPT ![w2].color = rot1.n[par].color,
                                                                       ![par].color = "B",
                                                                       ![w2L].color = "B"]
                                               rot2 == RotRight(n2, rot1.r, par)
                                           IN [n |-> rot2.n, r |-> rot2.r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
```

- [ ] **Step 2: Add DeleteFixup (bounded 5 iterations)**

Insert after `DeleteFixIt`:

```tla
\* Bounded delete fixup: at most 5 iterations.
\* (px, xLeft) are parent hints for nil — pass Pof result from before transplant.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int, Int, Bool) => { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int, x: Int, px: Int, xLeft: Bool, done: Bool };
DeleteFixup(n, r, x, px, xLeft) ==
    LET s1 == DeleteFixIt(n, r, x, px, xLeft)
        s2 == IF ~s1.done THEN DeleteFixIt(s1.n, s1.r, s1.x, s1.px, s1.xLeft) ELSE s1
        s3 == IF ~s2.done THEN DeleteFixIt(s2.n, s2.r, s2.x, s2.px, s2.xLeft) ELSE s2
        s4 == IF ~s3.done THEN DeleteFixIt(s3.n, s3.r, s3.x, s3.px, s3.xLeft) ELSE s3
        s5 == IF ~s4.done THEN DeleteFixIt(s4.n, s4.r, s4.x, s4.px, s4.xLeft) ELSE s4
    IN s5
```

- [ ] **Step 3: Commit**

```bash
git add examples/RB-Tree/RBT.tla
git commit -m "feat: add DeleteFixIt and DeleteFixup operators"
```

---

### Task 4: Add Delete operator and update Next

**Files:**
- Modify: `examples/RB-Tree/RBT.tla` — insert `Delete` after `Insert`, update `Next`

- [ ] **Step 1: Add Delete(key) operator**

Insert after `Insert` (after line 215, before `Next` comment):

```tla
\* ---------------------------------------------------------------------------
\* Deterministic Delete — standard RB-tree algorithm.
\* ---------------------------------------------------------------------------
Delete(key) ==
    Delete::
    /\ IF key \notin TreeKeys
       THEN /\ UNCHANGED <<nodes, root, step_count>>
            /\ action_taken' = "delete"
       ELSE
           LET z == BSTFind(nodes, root, key)
               hasTwoChildren == nodes[z].left /= nil /\ nodes[z].right /= nil
               y == IF hasTwoChildren THEN Successor(nodes, z) ELSE z
               x == IF nodes[y].left /= nil THEN nodes[y].left ELSE nodes[y].right
               n0 == IF hasTwoChildren
                     THEN [nodes EXCEPT ![z].key = nodes[y].key]
                     ELSE nodes
               yOldParent == Pof(n0, root, y)
               yIsLeft == yOldParent /= nil /\ n0[yOldParent].left = y
               yColor == IF hasTwoChildren THEN nodes[y].color ELSE nodes[z].color
               n1 == IF yOldParent = nil
                     THEN n0
                     ELSE IF yIsLeft
                          THEN [n0 EXCEPT ![yOldParent].left = x]
                          ELSE [n0 EXCEPT ![yOldParent].right = x]
               r1 == IF y = root THEN x ELSE root
               delFix == IF yColor = "B"
                         THEN LET fx == IF x = nil
                                        THEN yOldParent
                                        ELSE x
                                      fxPx == IF x = nil THEN yOldParent ELSE nil
                                      fxLeft == yIsLeft
                                  IN DeleteFixup(n1, r1, fx, fxPx, fxLeft)
                         ELSE [n |-> n1, r |-> r1, done |-> TRUE]
               n2 == [delFix.n EXCEPT ![delFix.r].color = "B"]
               finalNodes == RecomputeBH(n2)
           IN /\ nodes' = finalNodes
              /\ root' = delFix.r
              /\ Inv'
              /\ action_taken' = "delete"
              /\ step_count' = step_count + 1
```

- [ ] **Step 2: Update Next to include Delete**

Replace `Next` (lines 220-222):

```tla
Next ==
    \/ \E key \in KEYS: Insert(key)
    \/ \E key \in TreeKeys: Delete(key)
    \/ UNCHANGED <<nodes, root, action_taken, step_count>>
```

- [ ] **Step 3: Update TraceComplete for insert+delete scenarios**

Replace line 225:
```tla
TraceComplete == step_count < 6
```

- [ ] **Step 4: Commit**

```bash
git add examples/RB-Tree/RBT.tla
git commit -m "feat: add Delete operator and wire into Next"
```

---

### Task 5: Verify with Apalache parse

**Files:**
- None

- [ ] **Step 1: Run Apalache parse to check syntax and types**

```bash
java -jar apalache.jar parse examples/RB-Tree/RBT.tla
```

Expected: PASS with no errors

- [ ] **Step 2: Fix any parse/type errors if they occur, re-verify, commit fixes**

```bash
git add examples/RB-Tree/RBT.tla && git commit -m "fix: address Apalache parse errors for delete"
```

---

### Task 6: Verify end-to-end by running a small check

**Files:**
- None

- [ ] **Step 1: Run Apalache check on a small bounded model**

```bash
java -jar apalache.jar check --inv=TraceComplete --length=6 examples/RB-Tree/RBT.tla
```

Expected: No invariant violation (or check reports the expected bound stop)

- [ ] **Step 2: If check fails, read the counterexample, fix the code, re-run**

```bash
# Debug counterexample
java -jar apalache.jar check --inv=TraceComplete --length=6 --view=... examples/RB-Tree/RBT.tla
```

- [ ] **Step 3: Commit any fixes**

```bash
git add examples/RB-Tree/RBT.tla && git commit -m "fix: address model checker findings for delete"
```
