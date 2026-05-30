--------------------- MODULE RBT --------------------------
EXTENDS Integers

CONSTANTS
    \* The set of keys that may be inserted into the tree.
    \* @type: Set(Int);
    KEYS,
    \* Maximum number of non-nil nodes in the tree (for bounded checking).
    \* @type: Int;
    MAX_NODES

\* Node ID 0 is the NIL sentinel; real nodes use IDs 1..MAX_NODES.
nil == 0
NodeSet == {nil} \union (1..MAX_NODES)

\* Bounded sets for model checking.
Colors == {"R", "B"}
KeyVals == KEYS \union {0}
BhVals == 0..MAX_NODES

VarRecSet == [key: KeyVals, color: Colors, left: NodeSet, right: NodeSet, bh: BhVals]
NodeFunSet == [NodeSet -> VarRecSet]

VARIABLES
    \* Maps each node ID to its record. Unused nodes have key = 0
    \* and point left/right to nil.
    \* @type: Int -> { key: Int, color: Str, left: Int, right: Int, bh: Int };
    nodes,
    \* The ID of the root node (nil for empty tree).
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

\* The set of keys stored in the tree.
TreeKeys == { nodes[id].key : id \in NonNilSet }

\* ---------------------------------------------------------------------------
\* Red-Black tree invariants on the current state (nodes, root).
\* ---------------------------------------------------------------------------

\* The nil node is always the NilRec.
NilInv == nodes[nil] = NilRec

\* Root is black (or nil).
RootBlack == (root = nil) \/ (nodes[root].color = "B")

\* No red node has a red child.
NoDoubleRed ==
    \A id \in NonNilSet:
        nodes[id].color = "R"
            => (nodes[id].left = nil \/ nodes[nodes[id].left].color = "B")
               /\ (nodes[id].right = nil \/ nodes[nodes[id].right].color = "B")

\* BST property: for every non-nil node, left key < node key < right key.
BSTInv ==
    \A id \in NonNilSet:
        (nodes[id].left = nil \/ nodes[nodes[id].left].key < nodes[id].key)
        /\ (nodes[id].right = nil \/ nodes[id].key < nodes[nodes[id].right].key)

\* Black-height consistency: children have equal bh, and a node's bh
\* is its children's bh plus 1 if the node is black.
BHInv ==
    \A id \in NonNilSet:
        LET l == nodes[id].left
            r == nodes[id].right
        IN nodes[l].bh = nodes[r].bh
           /\ nodes[id].bh = nodes[l].bh + (IF nodes[id].color = "B" THEN 1 ELSE 0)

\* Composite RB-tree invariant.
Inv == NilInv /\ RootBlack /\ NoDoubleRed /\ BSTInv /\ BHInv

\* ---------------------------------------------------------------------------
\* Initial state: empty tree (only the nil sentinel exists).
\* ---------------------------------------------------------------------------
Init ==
    /\ nodes = [id \in NodeSet |->
        [key |-> 0, color |-> "B", left |-> nil, right |-> nil, bh |-> 0]]
    /\ root = nil
    /\ action_taken = "init"
    /\ step_count = 0

\* ---------------------------------------------------------------------------
\* Insert operation (atomic):
\*   - if key already present, nothing changes
\*   - otherwise, nondeterministically pick a new valid RB tree
\*     that contains all the old keys plus the new key.
\* ---------------------------------------------------------------------------
Insert(key) ==
    Insert::
    /\ IF key \in TreeKeys
       THEN UNCHANGED <<nodes, root, action_taken, step_count>>
       ELSE
           /\ nodes' \in NodeFunSet
           /\ root' \in NodeSet
           /\ nodes' /= nodes
           /\ Inv'
           /\ TreeKeys' = TreeKeys \union {key}
           /\ action_taken' = "insert"
           /\ step_count' = step_count + 1

\* ---------------------------------------------------------------------------
\* Next-state relation.
\* ---------------------------------------------------------------------------
Next ==
    \/ \E key \in KEYS: Insert(key)
    \/ UNCHANGED <<nodes, root, action_taken, step_count>>

\* Bounded model checking: stop after 3 insertions.
TraceComplete == step_count < 3

\* Constant initialization for model checking.
ConstInit == KEYS = {1, 2, 3, 4, 5} /\ MAX_NODES = 5

===========================================================
