---- MODULE RBT_Trace ----
EXTENDS Integers, Sequences, TraceData

MAX_NODES == 4
nil == 0
NodeSet == {nil} \union (1..MAX_NODES)

\* @type: Int;
VARIABLE pos

\* Access the nodes function from trace entry p.
\* TraceLog[p].nodes is a Seq({ key: Int, color: Str, left: Int, right: Int, bh: Int })
\* with entry 0 at position 1 (TLA+ 1-indexed).
NodesOf(p) ==
    [id \in NodeSet |-> TraceLog[p].nodes[id + 1]]

\* Reconstructed variables for invariant checking.
RootOf(p) == TraceLog[p].root

KeyOf(p, id) == NodesOf(p)[id].key
ColOf(p, id) == NodesOf(p)[id].color
LefOf(p, id) == NodesOf(p)[id].left
RigOf(p, id) == NodesOf(p)[id].right
BhOf(p, id)  == NodesOf(p)[id].bh

NonNilOf(p) == { id \in NodeSet \ {nil} : KeyOf(p, id) /= 0 }

NilInv(p) ==
    NodesOf(p)[nil] = [key |-> 0, color |-> "B", left |-> nil, right |-> nil, bh |-> 0]

RootBlack(p) ==
    (RootOf(p) = nil) \/ (ColOf(p, RootOf(p)) = "B")

NoDoubleRed(p) ==
    \A id \in NonNilOf(p):
        ColOf(p, id) = "R"
            => (LefOf(p, id) = nil \/ ColOf(p, LefOf(p, id)) = "B")
               /\ (RigOf(p, id) = nil \/ ColOf(p, RigOf(p, id)) = "B")

BSTInv(p) ==
    \A id \in NonNilOf(p):
        (LefOf(p, id) = nil \/ KeyOf(p, LefOf(p, id)) < KeyOf(p, id))
        /\ (RigOf(p, id) = nil \/ KeyOf(p, id) < KeyOf(p, RigOf(p, id)))

BHInv(p) ==
    \A id \in NonNilOf(p):
        LET l == LefOf(p, id)
            r == RigOf(p, id)
        IN BhOf(p, l) = BhOf(p, r)
           /\ BhOf(p, id) = BhOf(p, l) + (IF ColOf(p, id) = "B" THEN 1 ELSE 0)

Inv(p) == NilInv(p) /\ RootBlack(p) /\ NoDoubleRed(p) /\ BSTInv(p) /\ BHInv(p)

TraceConstInit == TRUE

TraceInit ==
    /\ pos = 1
    /\ Inv(pos)

TraceNext ==
    /\ pos < Len(TraceLog)
    /\ pos' = pos + 1
    /\ Inv(pos')

\* Inverted invariant: violation when trace is fully consumed => trace is valid.
TraceFinished == pos < Len(TraceLog)
====
