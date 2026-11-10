# PCWN_ HANDOFF: phase P5e (OPEN definitions, fourth module batch)

Target not yet established. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (Pool b936275). Branch codex/pc-prov-p5e-20261110, host workspace /home/dombarker/project-offloads/codex-pc-prov-p5e-20261110/. No ledger row, trust row, RSL, contract or shipped source changed; no trust row added; nothing pushed or merged.
Scopes: 21 Lean (PCWN_SCOPES.json; every one at most 21 s wall, peak RSS about 2.6 GB, swap 0, one at a time, caps unraised), 0 extraction (existing frozen emissions reused with their PINS; hashes in PCWN_TOOLS.json). Cargo jobs not applicable.

## Item 1: public_bytes, abbrev removed (EQUALITY_PROVED)
PRVEq_PB_w3.lean, scope PCWN_L004 exit 0. The new Aeneas library (0d21a9ec, Convert.lean sha256 e2586558...) does not only rename the constant: it types the residual with Never where the gate library uses core.convert.Infallible. Two distinct empty types, so a literal equality of the constants is ill-typed. Proved instead, unconditionally and with standard axioms: PCWN_NewLib.from_residual_eq (new from_residual after the empty-type map = gate from_residual) and PCWN_NewLib.branch_bind (bind of the new branch = bind of the gate branch given agreement on the Continue arm and the Break (Err e) arm). The fresh text now calls the verbatim new-library branch and from_residual (copied into PCWN_NewLib, attributes omitted), and all nine fresh = gate theorems hold; frontier and public_bytes use the pb_chain tactic built on branch_bind. No row named. L001 and L002 were failed probes (macro syntax, missing funext); L004 only added heartbeat resets.

## Settled by this job (exit 0, standard axioms)
- QRaw Types (AspisR1CanonicalQRawUnified.Types, FIo_QRawTypes): canonical.Q (rfl) and closure_2 (rfl; Unit); L005, L006.
- NEI_PushRaw.Types: M31, CM31, QM31, BatchedWeights (Equiv); L014 (L007 was the first pass without BatchedWeights).
- Stage2ContinuationTypes: Arity, Accumulator, BatchedWeights, Prepared, View (Equiv); L013. Fresh input is composite: PCVX_E012 plus the WideExact structure from PCVJ_E002 (aspis-core), both frozen 4bb3b3f.
- AspisR1CanonicalDotFinish.Funs: P, reduce, Q.limbs, Dot.finish (L010, derived from the PCVZ EbyKFinish file; Dot.finish by the PCVZ map4_mon shape). Also DotFinish.Types canonical.Q (L016).
- Outside the 12 modules: EbyKFinish.Types EbyKDot, Dot, Q (L015) and EbyKFinish.Funs EbyKDot.finish (L017, fresh = E015 EbyKDot::finish with the aspis-core from_limbs text).
- S8Kani2MutableSource BatchedWeights.value (L020): fresh = frozen E015 value with the P2f aspis-core reduce_u64 text, by arr4/map4_mon/idx_make4.
- FinishCandidateExplicitOps closure FnOnce instance and call_once (L021), rfl; Error and closure types are text-identical aliases only.
- New generic lemmas: PRVEq_PCWN_TE (Array/Vec/Slice transport, L011), used by the generator for composite field types.
Already settled by merged P3w and recorded without re-proof: Q.raw and closure_2.call in both QRaw Funs modules.

## Still OPEN, by cause (PCWN_TRIAGE.json has all 59 keys)
- NEI_PushRaw.Funs update_residue_row, BatchedWeights.push: DEPENDS_ON_LIBRARY_TRUST (HM-B). The fresh text uses the template into_iter (back : IterMut T -> Array T N); the gate uses a hand-repaired model whose back takes a transformer (NEG_RowIsolated FunsExternal comment). L012: type mismatch at into_iter_back. Names: MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter, core.slice.iter.IteratorIterMut.next. loop1 and loop1.body stay a PCVZ loop-return refinement, not an equality.
- QRaw closure/closure_1 (Funs call_mut/call_once and Types): GATE_ONLY_HELPER, no frozen counterpart.
- CurrentClaimDotModel (6): CANNOT_EXTRACT, Aeneas "Returns inside of nested loops are not supported yet" (prepared_claim, verifier.rs 53-68; PCWH_E008/E010). prepared_claim_dot* is a gate-only decomposition of the same function. Route: the approved Aeneas patch for nested-loop returns.
- S8Kani2MutableSource finish, finish_loop, finish_loop.body: NO_FRESH_EMISSION (iter_mut().enumerate() does not extract; slice-iterator roots belong to PCWH_). push, push_loop.body: source-shape difference plus the same HM-B model.
- FinishCandidateExplicitOps finish_query_dot, loop, body, finish_relation_round: PARAMETRIC_OPS (gate takes FinishOps) plus, for the loop, a pending_return transformation (gate applies finishDot after the loop, the frozen loop calls EbyKDot::finish inside it). Missing: an Ops instance from fresh emissions and a loop lemma with an effectful final step; the result would be CONDITIONAL_ON_BINDING.
- Port3_NativeBatchBody (5): PARAMETRIC_OPS and no fresh emission at the gate configuration. The gate uses wrapping_add/sub on plain operators (overflow-checks OFF); PCVX_E012/E013 are ON.

## Caveats
Funs files use alias identification for Dot/Q/Error/closure types; Types proofs back Dot and Q (L016, L005/L006), not Error or the finish closure. No difference at a matching configuration was found.

## Next
Run the Aeneas patch job and extract prepared_claim; settle HM-B identification of the two iterator models, then NEI and S8Kani2 push; build Ops instances for finish_relation_round and finish_query_dot*; extract batch_tree/batch_merkle at overflow-checks OFF.

Target not yet established.
