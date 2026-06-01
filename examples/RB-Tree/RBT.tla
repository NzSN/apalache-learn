--------------------- MODULE RBT --------------------------
EXTENDS Integers

\* The set of keys that may be inserted into the tree.
KEYS == {1, 2, 3, 4, 5}

\* Maximum number of non-nil nodes in the tree (for bounded checking).
MAX_NODES == 5

\* Node ID 0 is the NIL sentinel; real nodes use IDs 1..MAX_NODES.
nil == 0
NodeSet == {nil} \union (1..MAX_NODES)

VARIABLES
    \* @type: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int };
    nodes,
    \* @type: Int;
    root,
    \* @type: Str;
    action_taken,
    \* @type: Int;
    step_count

\* The record for the nil sentinel.
NilRec == [key |-> 0, color |-> "B", left |-> nil, right |-> nil, bh |-> 0]

\* The set of node IDs that are currently in the tree (have a non-zero key).
NonNilSet == { id \in NodeSet \ {nil} : nodes[id].key /= 0 }

TreeKeys == { nodes[id].key : id \in NonNilSet }

\* ---------------------------------------------------------------------------
\* Red-Black tree invariants
\* ---------------------------------------------------------------------------
NilInv == nodes[nil] = NilRec
RootBlack == (root = nil) \/ (nodes[root].color = "B")
NoDoubleRed ==
    \A id \in NonNilSet:
        nodes[id].color = "R"
            => (nodes[id].left = nil \/ nodes[nodes[id].left].color = "B")
               /\ (nodes[id].right = nil \/ nodes[nodes[id].right].color = "B")
BSTInv ==
    \A id \in NonNilSet:
        (nodes[id].left = nil \/ nodes[nodes[id].left].key < nodes[id].key)
        /\ (nodes[id].right = nil \/ nodes[id].key < nodes[nodes[id].right].key)
BHInv ==
    \A id \in NonNilSet:
        LET l == nodes[id].left
            r == nodes[id].right
        IN nodes[l].bh = nodes[r].bh
           /\ nodes[id].bh = nodes[l].bh + (IF nodes[id].color = "B" THEN 1 ELSE 0)
Inv == NilInv /\ RootBlack /\ NoDoubleRed /\ BSTInv /\ BHInv

\* ---------------------------------------------------------------------------
\* Deterministic RB-tree helpers (module-level for type annotation support).
\* NRec = { key: Int, color: Str, left: Int, right: Int, bh: Int }
\* Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int } = Int -> NRec
\* ---------------------------------------------------------------------------

\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }) => Int;
FindUnused(n) ==
    LET unused == { id \in 1..MAX_NODES : n[id].key = 0 }
    IN CHOOSE id \in unused : \A j \in unused : id <= j

\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int) => Int;
Pof(n, r, id) ==
    IF id = r THEN nil
    ELSE CHOOSE p \in NodeSet : n[p].left = id \/ n[p].right = id

\* BST parent for key insertion (unrolled traversal, depth ≤ 3).
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int) => Int;
BSTParent(n, r, key) ==
    IF r = nil THEN nil
    ELSE IF (key < n[r].key /\ n[r].left = nil)
            \/ (key > n[r].key /\ n[r].right = nil)
         THEN r
         ELSE LET c1 == IF key < n[r].key THEN n[r].left ELSE n[r].right
              IN IF c1 = nil THEN r
                 ELSE IF (key < n[c1].key /\ n[c1].left = nil)
                         \/ (key > n[c1].key /\ n[c1].right = nil)
                      THEN c1
                       ELSE c1

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

\* In-order successor of id (min of right subtree). Bounded depth ≤ 3.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int) => Int;
Successor(n, id) ==
    LET r == n[id].right
    IN IF r = nil THEN nil
       ELSE IF n[r].left = nil THEN r
       ELSE IF n[n[r].left].left = nil THEN n[r].left
       ELSE n[n[r].left].left

\* Rotate left at x. Returns [n |-> Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r |-> Int].
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int) => { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int };
RotLeft(n, r, x) ==
    LET y == n[x].right
    IN IF y = nil THEN [n |-> n, r |-> r]
       ELSE LET p == Pof(n, r, x)
                n1_ == [n EXCEPT ![x].right = n[y].left]
                n2_ == [n1_ EXCEPT ![y].left = x]
                newR == IF x = r THEN y ELSE r
                n3_ == IF x = r THEN n2_
                       ELSE IF n[p].left = x
                            THEN [n2_ EXCEPT ![p].left = y]
                            ELSE [n2_ EXCEPT ![p].right = y]
            IN [n |-> n3_, r |-> newR]

\* Rotate right at x. Returns [n |-> Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r |-> Int].
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int) => { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int };
RotRight(n, r, x) ==
    LET y == n[x].left
    IN IF y = nil THEN [n |-> n, r |-> r]
       ELSE LET p == Pof(n, r, x)
                n1_ == [n EXCEPT ![x].left = n[y].right]
                n2_ == [n1_ EXCEPT ![y].right = x]
                newR == IF x = r THEN y ELSE r
                n3_ == IF x = r THEN n2_
                       ELSE IF n[p].left = x
                            THEN [n2_ EXCEPT ![p].left = y]
                            ELSE [n2_ EXCEPT ![p].right = y]
            IN [n |-> n3_, r |-> newR]

\* Single fixup iteration (non-recursive). Returns { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int, z: Int, done: Bool }.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int) => { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int, z: Int, done: Bool };
FixIt(n, r, z) ==
    LET par == Pof(n, r, z)
    IN IF par = nil \/ n[par].color = "B"
       THEN [n |-> n, r |-> r, z |-> z, done |-> TRUE]
       ELSE LET gp == Pof(n, r, par)
            IN IF gp = nil
               THEN [n |-> n, r |-> r, z |-> z, done |-> TRUE]
               ELSE LET pLeft  == n[gp].left = par
                        uncle  == IF pLeft THEN n[gp].right ELSE n[gp].left
                        uRed   == uncle /= nil /\ n[uncle].color = "R"
                    IN IF uRed
                       THEN LET nA == [n EXCEPT ![par].color = "B",
                                                  ![uncle].color = "B",
                                                  ![gp].color = "R"]
                            IN [n |-> nA, r |-> r, z |-> gp, done |-> FALSE]
                       ELSE IF pLeft
                            THEN IF z = n[par].right
                                 THEN LET rr  == RotLeft(n, r, par)
                                          z2  == par
                                          p2  == Pof(rr.n, rr.r, z2)
                                          gp2 == Pof(rr.n, rr.r, p2)
                                          nA  == [rr.n EXCEPT ![p2].color = "B",
                                                                ![gp2].color = "R"]
                                          rr2 == RotRight(nA, rr.r, gp2)
                                      IN [n |-> rr2.n, r |-> rr2.r, z |-> z2, done |-> TRUE]
                                 ELSE LET nA  == [n EXCEPT ![par].color = "B",
                                                              ![gp].color = "R"]
                                          rr2 == RotRight(nA, r, gp)
                                      IN [n |-> rr2.n, r |-> rr2.r, z |-> z, done |-> TRUE]
                            ELSE IF z = n[par].left
                                 THEN LET rr  == RotRight(n, r, par)
                                          z2  == par
                                          p2  == Pof(rr.n, rr.r, z2)
                                          gp2 == Pof(rr.n, rr.r, p2)
                                          nA  == [rr.n EXCEPT ![p2].color = "B",
                                                                ![gp2].color = "R"]
                                          rr2 == RotLeft(nA, rr.r, gp2)
                                      IN [n |-> rr2.n, r |-> rr2.r, z |-> z2, done |-> TRUE]
                                 ELSE LET nA  == [n EXCEPT ![par].color = "B",
                                                              ![gp].color = "R"]
                                          rr2 == RotLeft(nA, r, gp)
                                      IN [n |-> rr2.n, r |-> rr2.r, z |-> z, done |-> TRUE]

\* Bounded fixup: at most 5 iterations.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int) => { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int, z: Int, done: Bool };
Fixup(n, r, z) ==
    LET s1 == FixIt(n, r, z)
        s2 == IF ~s1.done THEN FixIt(s1.n, s1.r, s1.z) ELSE s1
        s3 == IF ~s2.done THEN FixIt(s2.n, s2.r, s2.z) ELSE s2
        s4 == IF ~s3.done THEN FixIt(s3.n, s3.r, s3.z) ELSE s3
        s5 == IF ~s4.done THEN FixIt(s4.n, s4.r, s4.z) ELSE s4
    IN s5

\* Recompute black heights: 3 passes (sufficient for depth ≤ 3).
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }) => Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int };
RecomputeBH(n) ==
    LET n1 == [id \in NodeSet |-> IF id = nil \/ n[id].key = 0 THEN n[id]
                ELSE [n[id] EXCEPT !.bh = n[n[id].left].bh + (IF n[id].color = "B" THEN 1 ELSE 0)]]
        n2 == [id \in NodeSet |-> IF id = nil \/ n1[id].key = 0 THEN n1[id]
                ELSE [n1[id] EXCEPT !.bh = n1[n1[id].left].bh + (IF n1[id].color = "B" THEN 1 ELSE 0)]]
        n3 == [id \in NodeSet |-> IF id = nil \/ n2[id].key = 0 THEN n2[id]
                ELSE [n2[id] EXCEPT !.bh = n2[n2[id].left].bh + (IF n2[id].color = "B" THEN 1 ELSE 0)]]
    IN n3

\* Single delete-fixup iteration. (px, xLeft) are parent hints for the nil case;
\* pass (nil, FALSE) when x is a real node (Pof is used instead).
\* Returns { n, r, x, px, xLeft, done }.
\* @type: (Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, Int, Int, Int, Bool) => { n: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int }, r: Int, x: Int, px: Int, xLeft: Bool, done: Bool };
DeleteFixIt(n, r, x, px, xLeft) ==
    LET par == IF px /= nil THEN px ELSE Pof(n, r, x)
        isLeft == IF px /= nil THEN xLeft ELSE (par /= nil /\ n[par].left = x)
    IN IF x = r \/ (x /= nil /\ n[x].color = "R")
       THEN [n |-> [n EXCEPT ![x].color = "B"], r |-> r, x |-> x, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
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
                         IN [n |-> rot.n, r |-> rot.r, x |-> x, px |-> par, xLeft |-> isLeft, done |-> FALSE]
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

\* ---------------------------------------------------------------------------
\* Initial state: empty tree.
\* ---------------------------------------------------------------------------
Init ==
    /\ nodes = [id \in NodeSet |->
        [key |-> 0, color |-> "B", left |-> nil, right |-> nil, bh |-> 0]]
    /\ root = nil
    /\ action_taken = "init"
    /\ step_count = 0

\* ---------------------------------------------------------------------------
\* Deterministic Insert — same algorithm as Rust rb_tree.rs insert().
\* ---------------------------------------------------------------------------
Insert(key) ==
    Insert::
    /\ IF key \in TreeKeys
       THEN /\ UNCHANGED <<nodes, root, step_count>>
            /\ action_taken' = "insert"
       ELSE
           LET newId == FindUnused(nodes)
               n0    == [nodes EXCEPT ![newId] =
                           [key |-> key, color |-> "R", left |-> nil, right |-> nil, bh |-> 0]]
               parent == BSTParent(n0, root, key)
               n1    == IF parent = nil THEN n0
                        ELSE IF key < n0[parent].key
                             THEN [n0 EXCEPT ![parent].left = newId]
                             ELSE [n0 EXCEPT ![parent].right = newId]
               r1    == IF root = nil THEN newId ELSE root
               fRes  == Fixup(n1, r1, newId)
               n2    == [fRes.n EXCEPT ![fRes.r].color = "B"]
               finalNodes == RecomputeBH(n2)
           IN /\ nodes' = finalNodes
              /\ root' = fRes.r
              /\ Inv'
              /\ action_taken' = "insert"
               /\ step_count' = step_count + 1

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
               n1clean == [n1 EXCEPT ![y].key = 0]
               r1 == IF y = root THEN x ELSE root
               delFix == IF yColor = "B"
                         THEN LET fx == IF x = nil
                                        THEN nil
                                        ELSE x
                                      fxPx == IF x = nil THEN yOldParent ELSE nil
                                      fxLeft == yIsLeft
                                  IN DeleteFixup(n1clean, r1, fx, fxPx, fxLeft)
                         ELSE [n |-> n1clean, r |-> r1, x |-> nil, px |-> nil, xLeft |-> FALSE, done |-> TRUE]
               n2 == [delFix.n EXCEPT ![delFix.r].color = "B"]
               finalNodes == RecomputeBH(n2)
           IN /\ nodes' = finalNodes
              /\ root' = delFix.r
              /\ Inv'
              /\ action_taken' = "delete"
              /\ step_count' = step_count + 1

\* ---------------------------------------------------------------------------
\* Next-state relation.
\* ---------------------------------------------------------------------------
Next ==
    \/ \E key \in KEYS: Insert(key)
    \/ \E key \in TreeKeys: Delete(key)
    \/ UNCHANGED <<nodes, root, action_taken, step_count>>

\* Bounded model checking: stop after 6 steps.
TraceComplete == step_count < 6

==========================================================
