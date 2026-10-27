# Stage 3: both physical traces and checked actual-root source extraction

CPH_Game.field(d) now records BOTH TX1's suffix after the actual CP copy AND
TX2's actions from its loaded bank. The prior CPG projection contained only the
former. CPH_Trace.derive constructs both source/observed-bank/event equations
from those two state-threaded traces; both tops export this instance. No fifth
field, additional trace hypothesis, byte equality, history guard or program pin
was introduced. Own objects were snapshotted in CPH_two_trace_snapshot before
changing that record and its same-prefix dependent closure; other-prefix
objects were not changed.

CPH_Rc2Source.source is extracted from the CHECKED Rc2_Top.deployed body and its
T2R_Top predecessor. CPH_Extract is a proof-refactoring tactic: it inlines only
those two existing theorem bodies, selects driver/dictionary/source/copy/events/
protection conjuncts, and refuses any remaining metavariable for an unprovided
legacy argument. It constructs an ordinary Lean proof term; the kernel and
#print axioms validate it. This does NOT infer an unconditional source fact
from an arbitrary implication with an unproved frozen2 premise. Rather, the
existing checked proof body's source branch does not use those headline inputs.
CPH_Pair now consumes THIS actual-root source result and CPH_Close.from_rc2,
replacing the earlier independently reconstructed T2R_Pair path. Final root72
has only standard axioms, with no old frozen2 headline inputs or program pin.

The joint runtime fixture is substantially stronger than CPG's aliased fixture:
separate CP/proof/public cells, bounded-injective keys, both exact entry-admission
records, the approved SDK/std consistency models, both wrappers evaluating inner
Ok, a funded CP, nonempty credit/live-reap/rollback suffix, derived copy bytes,
actual reader bytes, and a constructed CheckpointVersionBinding over the same
physical events. CPH_Nonvacuity.joint_runtime combines them. Its n1/n2 functions
are explicitly local witnesses; no extraction to the installed crypto source or
joint inhabitation of every retained headline/source premise is claimed.

One barrier race at attempt66 referenced another vanished cgroup; the required
30-second wait and single retry succeeded, without changing the barrier. One
pre-scope missing own dependency at24 ran no Lean; it was resolved by compiling
that changed proof. Ordinary elaboration/namespace/definitional-reduction
failures are preserved; failed sorryAx recovery audits are excluded. Generic
wrapper construction replaced concrete normalization after maxRecDepth errors;
no depth, heartbeat, RAM or task cap was raised. No memory kill or wall timeout.
