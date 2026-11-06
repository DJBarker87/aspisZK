import NHL_Tx1Stages
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_Tx1Stages
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Out := NHL_Tx1Stages.Out
abbrev QueryOut := core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error

/-- Literal query-loop return boundary. Full accumulator and pending carrier
are passed to finish/checkpoint; rejection has no suffix. Source support only. -/
def afterQuery (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (public_bytes proof : Slice U8) (hash : H) (p : verifier.Prepared)
 (r : QueryOut) : Result Out := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue pair => NHL_Tx1Stages.afterQuery ops D public_bytes proof hash none p pair.1 pair.2
 | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual

theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H) (c : NHL_Tx1Stages.Context) :
 NHL_Tx1Stages.queryCut ops D public_bytes proof k hash none c =
 (do let r ← ops.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k
     afterQuery ops D public_bytes proof hash c.prepared r) := by rfl

theorem query_error (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (public_bytes proof : Slice U8) (hash : H) (p : verifier.Prepared) (e : verifier.Error) :
 afterQuery ops D public_bytes proof hash p (.Err e)=ok (.Err e) := by rfl

/-- The writer reconstruction preserves rhs, power and next by construction;
this theorem does not assume pending.finish's mutable footprint. -/
theorem writer_frame (a : verifier.Accumulator) (weights : alloc.vec.Vec aspis_core.field.QM31) :
 ({a with weights:=weights} : verifier.Accumulator).rhs=a.rhs ∧
 ({a with weights:=weights} : verifier.Accumulator).power=a.power ∧
 ({a with weights:=weights} : verifier.Accumulator).next=a.next := by exact ⟨rfl,rfl,rfl⟩
#print axioms factor
#print axioms query_error
#print axioms writer_frame
#print factor
end AspisR1.NKQ_Tx1Stages
end
