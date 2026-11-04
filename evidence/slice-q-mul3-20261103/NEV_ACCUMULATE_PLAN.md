# Accumulation stage — active, no closure claim

The prefix stage is committed at `2ac3ce2af3`. Accumulation is next in the
binding order. Its exact currently open tasks are:

1. Finish the small outside-slice `CodeField<WideExact>::from_m31` bridge.
   Actual constructor extraction E001 is successful and Types/Funs compile
   (L010/L011). Native K030 succeeds and original-name K031 negative control
   fails. L012 has not launched: host admission refuses the timing quiet
   window, exit 78 / allowed false. Its Lean bridge reuses S1's generic
   all-word remainder theorem; `NEV_CodeFieldUse.basis_call` derives the
   canonical domain from the SAME returned production basis and SAME read.
2. Bind imported E005 actual-body extraction to concrete CLOSED field and
   push callees. `NEV_ACCUMULATE_IMPORT.json` records only nominal namespace
   changes. External definitions contain no axioms. They currently are source
   drafts, not successful Lean checks or discharged call edges.
3. Compile complete-carrier round trips for all Prepared/Accumulator fields,
   both vector and array contents, and BatchedWeights. No projection omits
   unused or unchanged fields.
4. Native ONE basis iteration and ONE outer scalar update: local product call
   records, no field multiplication, original-name failing controls, exact KMX
   patch. `NEV_BasisRaw` associates the new emitted checked inner body and loop
   with retained NBF/S7 control flow. It does not reprove basis arithmetic.
5. Bind row borrow/trace/index context and tail call arguments/returns using
   local records, preserving errors and mutable frames. Reuse the already
   proved NEI push/residue packet and independent global/local counters.
6. Establish every actual input domain, all row phases, full Result/state/
   effect association; then run the fail-closed slice validator. Only that
   composed result may close the two accumulation rows or incoming edges.

The distinct native/code-generation gates, not the mathematical recurrence,
are expected to consume the remaining Kani time. All scopes keep 6G/8G/0
swap/64 tasks. No changed full regression is repeated without a reason.

Own gate repair/addition: the exact cfg-only `NEV_arbitrary` module now also
implements arbitrary raw QM31 using four unrestricted raw M31 words. This
supports a full 64-element native weight-vector prestate for the tail frame.
The erasure gate still compares every frozen byte unchanged, accepting only
the single exact new cfg-only module body. No Cargo graph, feature, static,
copy-mitigation, tool, admission or lock checks were weakened. The new tail
source is a draft until its own fresh native/control pair validates.

L024 diagnosed a generated global instance collision: Aeneas's
`@[discriminant isize]` on the new raw `Variant` creates
`instDiscriminantVariantIsize`, already present in the coherent model's
AspisR1FinishRelationCurrent.Types. Only the new raw Types module is repaired:
its exact 0/1/2 tag interpretation has an explicitly NEV-named instance. The
Rust body is untouched and does not inspect Variant. Import provenance is
updated; the raw Types and affected new dependent modules are recompiled.
Earlier successful dependent objects are superseded after this source fix.

Progress after instance repair: L025 raw Types, L026 complete carrier round
trips, L027 concrete external bindings, L028 actual Funs, L029 actual inner
step/stop/loop association, L031 outer scalar/body association, and L032
nominal callee Result transports all pass with standard axioms only. L030
is an excluded syntax failure in the new nested-do proof; fixed by unfolding
the concrete binding rather than changing its statement. L021/L022 are
excluded tactic/numeral-transparency failures; L023/L029 solve the unchanged
statements with explicit reduction/transparency control, no new axiom.
Native K032/K033, K034/K035, K036/K037 are PASS / matched intended FAIL pairs.
The accumulation row and incoming edges still carry NO closure credit.

Native source review correction: K032/K033 used the frozen pure `basis_at`
wrapper at the inner basis read, whereas the actual inner Rust loop reads
`basis[j]` directly. Their original verdicts remain recorded, but the stricter
actual-inner credit now requires K038/K039 on the SAME harness name, after
replacing only that getter call by the literal native indexing expression.
This is a changed source-fidelity target, not an unchanged rerun, a rename,
a timeout retry, or a Kani tool finding. Row context moves to K040/K041.
