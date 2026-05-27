---------------------- MODULE Hanoi --------------------------
EXTENDS Integers, Sequences
CONSTANT
  \* @type: Int;
  DISKS

VARIABLE
  \* @type: Seq(Int);
  A,
  \* @type: Seq(Int);
  B,
  \* @type: Seq(Int);
  C,
  \* @type: Str;
  action_taken,
  \* @type: { from: Str, to: Str, disk: Int };
  nondet_picks,
  \* @type: Int;
  move_count

\* Top disk of a peg (the disk available to move).
\* Pegs are stored bottom-to-top, so the top is the last element.
TopDisk(peg) == peg[Len(peg)]

\* Remove the top disk from a peg.
PopDisk(peg) == SubSeq(peg, 1, Len(peg) - 1)

\* Add a disk to the top of a peg.
PushDisk(peg, disk) == Append(peg, disk)

\* A move is legal when the source is non-empty and the destination
\* is either empty or has a larger disk on top.
CanMove(src, dst) ==
  src /= <<>> /\ (dst = <<>> \/ TopDisk(src) < TopDisk(dst))

\* Initial state: all disks on peg A, largest at bottom.
HanoiInit ==
  /\ A = <<DISKS, DISKS-1, 1>>  \* e.g. DISKS=3: <<3, 2, 1>>
  /\ B = <<>>
  /\ C = <<>>
  /\ action_taken = "init"
  /\ nondet_picks = [from |-> "none", to |-> "none", disk |-> 0]
  /\ move_count = 0

\* Move from A to B.
MoveAtoB ==
  /\ CanMove(A, B)
  /\ A' = PopDisk(A)
  /\ B' = PushDisk(B, TopDisk(A))
  /\ C' = C
  /\ action_taken' = "move"
  /\ nondet_picks' = [from |-> "A", to |-> "B", disk |-> TopDisk(A)]
  /\ move_count' = move_count + 1

\* Move from A to C.
MoveAtoC ==
  /\ CanMove(A, C)
  /\ A' = PopDisk(A)
  /\ B' = B
  /\ C' = PushDisk(C, TopDisk(A))
  /\ action_taken' = "move"
  /\ nondet_picks' = [from |-> "A", to |-> "C", disk |-> TopDisk(A)]
  /\ move_count' = move_count + 1

\* Move from B to A.
MoveBtoA ==
  /\ CanMove(B, A)
  /\ A' = PushDisk(A, TopDisk(B))
  /\ B' = PopDisk(B)
  /\ C' = C
  /\ action_taken' = "move"
  /\ nondet_picks' = [from |-> "B", to |-> "A", disk |-> TopDisk(B)]
  /\ move_count' = move_count + 1

\* Move from B to C.
MoveBtoC ==
  /\ CanMove(B, C)
  /\ A' = A
  /\ B' = PopDisk(B)
  /\ C' = PushDisk(C, TopDisk(B))
  /\ action_taken' = "move"
  /\ nondet_picks' = [from |-> "B", to |-> "C", disk |-> TopDisk(B)]
  /\ move_count' = move_count + 1

\* Move from C to A.
MoveCtoA ==
  /\ CanMove(C, A)
  /\ A' = PushDisk(A, TopDisk(C))
  /\ B' = B
  /\ C' = PopDisk(C)
  /\ action_taken' = "move"
  /\ nondet_picks' = [from |-> "C", to |-> "A", disk |-> TopDisk(C)]
  /\ move_count' = move_count + 1

\* Move from C to B.
MoveCtoB ==
  /\ CanMove(C, B)
  /\ A' = A
  /\ B' = PushDisk(B, TopDisk(C))
  /\ C' = PopDisk(C)
  /\ action_taken' = "move"
  /\ nondet_picks' = [from |-> "C", to |-> "B", disk |-> TopDisk(C)]
  /\ move_count' = move_count + 1

Init == HanoiInit
Next == MoveAtoB \/ MoveAtoC \/ MoveBtoA \/ MoveBtoC \/ MoveCtoA \/ MoveCtoB

\* No larger disk rests on a smaller disk.
\* For each peg, the sequence must be strictly decreasing
\* (from bottom to top: largest first, smallest last).
Inv ==
  (A = <<>> \/ \A i \in 1..(Len(A)-1): A[i+1] < A[i])
  /\ (B = <<>> \/ \A i \in 1..(Len(B)-1): B[i+1] < B[i])
  /\ (C = <<>> \/ \A i \in 1..(Len(C)-1): C[i+1] < C[i])

\* Violated after 15 moves — Apalache treats the violation
\* as a counterexample (= the test trace).
\* 15 moves gives plenty of room for a 3-disk Hanoi puzzle
\* (optimal solution is 7 moves).
TraceComplete == move_count < 15

\* Constant initialization: pin DISKS to 3.
HanoiConstInit == DISKS = 3

============================================================
