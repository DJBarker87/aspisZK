import NKO_C08Source
set_option autoImplicit false
noncomputable section
namespace NKO_C08
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Install the retained native store induction on THAT actual pending and
mutable weight region. The source query supplies both64-cell widths. -/
theorem occurrence (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31)
 (reply : Result (Slice aspis_core.field.QM31))
 (entered : Event.flush pending weights reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 pending.raw.val.length=64 ∧ weights.val.length=64 ∧
 reply=ok (NJJ_Flush.output pending) ∧
 NKE_FlushNative.states pending weights 64=(NJJ_Flush.output pending).val ∧
 (∀ q∈NKE_FlushNative.states pending weights 64,Port3_FlushInstall.Canonical q) := by
 obtain ⟨rawSize,weightSize,value⟩ := source wr rr merkle finish d pub proof ck hash _ entered
 have native := NKE_FlushNative.source pending weights rawSize weightSize
 exact ⟨rawSize,weightSize,value,native.2⟩

/-- Every one-iteration native cut includes raw, terms and all other cells.
The arbitrary native value reply is instantiated by the CLOSED SAME-row law. -/
theorem row_at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31)
 (reply : Result (Slice aspis_core.field.QM31))
 (entered : Event.flush pending weights reply∈(run wr rr merkle finish d pub proof ck hash none).events)
 (i : Nat) (inside : i<64) (value : aspis_core.field.QM31)
 (child : (pending.raw.val[i]?).map NJJ_Flush.cell=some value) :
 NJR_Cuts.flushStep pending.raw.val pending.raw.val pending.terms pending.terms
 (NKE_FlushNative.states pending weights i) (NKE_FlushNative.states pending weights (i+1)) i value := by
 obtain ⟨rawSize,weightSize,_⟩ := source wr rr merkle finish d pub proof ck hash _ entered
 exact NKE_FlushNative.step pending weights rawSize weightSize i inside value child
#print axioms occurrence
#print axioms row_at_actual
end NKO_C08
