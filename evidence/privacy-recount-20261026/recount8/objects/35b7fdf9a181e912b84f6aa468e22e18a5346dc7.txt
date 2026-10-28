import R1Z.PV_RunJoin_PolyCell38
import R1Z.ProverRwDictionaryEmbedding
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningWord43
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

def read (ops : ExternalFuns) (word : host_commitment.Word) (i : Usize) : Result W :=
  match word with
  | .Base v => do
    let m ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31) v i
    let q ← @aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 _
      (ProverRwP6BodyCandidate.selected ops) m
    .ok (PV_RunJoin_PolyCell38.wide q)
  | .Secure v => do
    let q ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.QM31) v i
    .ok (PV_RunJoin_PolyCell38.wide q)

/-- Complete Result equality for every actual stored commitment word. Bounds
errors stay in the source vector read; all raw field normalization is retained. -/
theorem value (ops : ExternalFuns) (word : host_commitment.Word) (i : Usize) :
    @host_commitment.Word.value _ (ProverRwP6BodyCandidate.selected ops) word i=read ops word i := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  cases word with
  | Secure v =>
    unfold host_commitment.Word.value read
    apply congrArg (Aeneas.Std.bind _)
    funext q
    exact PV_RunJoin_PolyCell38.embed ops q
  | Base v =>
    unfold host_commitment.Word.value read
    apply congrArg (Aeneas.Std.bind _)
    funext m
    have composed : @aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 _
      (ProverRwP6BodyCandidate.selected ops) m=(do
        let q ← @aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 _
          (ProverRwP6BodyCandidate.selected ops) m
        @aspis_core.field.wide_exact.WideExact.from_qm31 _ (ProverRwP6BodyCandidate.selected ops) q) :=
      ProverRwDictionaryEmbedding.composition ops m
    rw [composed]
    apply congrArg (Aeneas.Std.bind _)
    funext q
    exact PV_RunJoin_PolyCell38.embed ops q
#print axioms value
end R1Z.PV_RunJoin_OpeningWord43
