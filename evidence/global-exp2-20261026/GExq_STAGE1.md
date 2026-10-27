# Stage 1: terminal P6 charged once per tree

Before: GExp_FinalAccepted.accepted_pair_unified, all-world native log <=22585;
GExp_CollisionBudget.replay_collision, 6*(Q0+Q1+23625)^2/2^256.
After: GExq_FinalAccepted.accepted_pair_unified, SAME hypothesis binders and
SAME existential f/s/cuts, all-world native log <=1921. Replay collision bound
GExq_CollisionBudget.replay_collision is 6*(Q0+Q1+1921+1040)^2/2^256.
Every collision and preprocessing/adaptive choice budget term remains explicit.

The new credit proof charges a continuing step <=1 leaf read and retains287
units of reserve; a terminal step consumes <=288. The actual loop fuel yields
<=300/tree, <=900/batch; TX1 <=115+900+3=1018, TX2 <=3+900=903. Bounds cover
all ideal worlds, rejected paths and duplicate reads. Native accepted-log
transport remains success-conditioned as before. No new acceptance restriction.
These are structural worst-case proofs, not fixture or attack-work measurements.

Ledger delta: L157 OPEN, L159 OPEN, full L088 OPEN; zero assigned rows removed.
No assumptions discharged/added/changed in the endpoint. In particular this
does not derive the restricted (Q+34) charge or the original byte-indexed join.
Non-vacuity: no new hypotheses; inherited GExp_Nonvacuity rejection/partial-hash
witnesses still apply to exactly the same source programs. No joint accepted
native/runtime fixture is newly claimed.

Attempts001..023 include failures001 (zero-add simplification),003 (heartbeat
limit),004 (namespace typo),007 (explicit-bind projection),011/013 (generic
Hash transport). 003 was split into an explicit typed tactic and revised body
(005/006); no unchanged timed-out rerun or increased cap. Generic Hash source
support is green in015/017/019/021 and prepares caller integration. Every
current theorem audited in these receipts uses only standard axioms. Exact
command, source/dependency hash, revision, status, wall, peak RSS, swaps, limits
and full axioms/errors are in per-attempt JSON/stdout/time. No package replay,
Rust/Kani/SBF run or shipped source change. Inherited ELF pins unchanged.
