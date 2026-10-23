# Constructor reverse-carry source semantics

This is source arithmetic/recurrence progress, beyond the earlier output-canonicality result. It interprets the same accepted executions of the generated constructor V3 source cut. The actual Rust iterator normalization, Box/runtime and caller boundaries remain as documented in the existing constructor source packets.

Proved:

- `CarryBodySemantics.carry_body_success_exact`: a successful actual carry body derives its iterator coordinate, source input read, mutable write, exact decoded carry product and exact cell formula. Child arithmetic successes are extracted from that same execution, not assumed separately. Existing current mul/add/sub semantics and canonical wrapping/checked maps are reused.
- `VectorMeaning.update_meaning`: the actual successful mutable write has exact decoded `Function.update` meaning. Existing actual Array readback lemmas are reused.
- `CarryMeaningStep.carry_step_meaning`: the same actual body preserves the symbolic invariant: carry equals the product of processed source coordinates; processed suffix contains successor-point values; unprocessed prefix retains original values.
- `CarryLoopSemantics.carry_loop_success_exact`: the whole actual accepted reverse loop returns a canonical vector with the symbolic successor recurrence at every successful read. The existing generic loop invariant and reverse-range progress proofs are reused.

The recurrence uses Nat coordinates in the same MSB-first order as the source. It follows the existing SemView/ProverCommitSuccessorPoint49 recurrence; transport to the imported retained SemView definition is a separate pending check, not claimed here. No large concrete recurrence is normalized.

The whole-loop theorem still explicitly assumes its INITIAL state invariant: canonical source/input and initial successor/carry, correct source-input read meaning, zero start/end at most ten, initial carry recurrence, and initial processed-suffix meaning. It also assumes that this actual loop succeeds. These are not claims that the full constructor's initialization or output semantics is already closed. Candidate follow-ups derive the input meaning from actual reads, discharge ONE/start/end initialization, and derive the complete same-call statement producer and both complement writes.

Whole S9, complete source-to-runtime correspondence, whole-constructor totality/R22, composed soundness and the 100-bit target remain OPEN. Source/body/import pins, resource receipts and standard-only axiom reports are included; no compiled artifacts are included.
