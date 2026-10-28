import NCI_QueryInvariant
import CheckpointBytes4SuccessfulFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_ResumeDomains
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Ops CheckpointBytes4Layout CheckpointBytes4ReaderFields

def Canonical (q : aspis_core.field.QM31) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

theorem sourceK_canonical (x : OraclePortCheckpointAbiC5.K) : Canonical (sourceK x) := by
  simp only [Canonical,sourceK,CheckpointBytes3Namespaces.fromK,CheckpointBytes3KDecode.rawK,
    CheckpointBytes3KDecode.rawLimbs,CheckpointBytes3ScalarShape.kWords,M31ParserRefinement.valueToU32_val]
  exact ⟨(RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 0).isLt,
    (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 1).isLt,
    (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 2).isLt,
    (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 3).isLt⟩

-- All domains below are DERIVED from the SAME successful model return.
-- Native call/bytes association is an open bridge, not an implicit assumption.
theorem returned_domains (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (ck proof publicInput : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (size : ck.val.length=1768)
    (success : verifier.resumeWithOps (ops reserved) D ck proof publicInput .S2 hash = ok (.Ok (p,a))) :
    (∀ q ∈ p.queries.val, q.val < 262144) ∧ p.queries.val.Nodup ∧
    a.weights.val.length=64 ∧ (∀ q ∈ a.weights.val, Canonical q) ∧
    Canonical a.power ∧ Canonical p.rho ∧ reserved=true ∧
    ∃ f : OraclePortCkptAbiSourceFields.Fields (ops reserved) ck .S2 p a,
      f.finalAt.val=1736 ∧ f.rPower.at.val=712 := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof publicInput .S2 hash p a success
  have flat := flat_fields reserved ck p a f size
  have validated : queryLoop [] p.queries.val = core.result.Result.Ok () := Result.ok.inj f.validate
  obtain ⟨weights,_,hweights⟩ := flat.weights
  have canonWeights : ∀ q ∈ a.weights.val, Canonical q := by
    rw [hweights]
    intro q hq
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hq
    exact sourceK_canonical x
  have lengthWeights : a.weights.val.length=64 := by rw [hweights]; simp
  have canonPower : Canonical a.power := by
    obtain ⟨x,_,hx⟩ := flat.power
    rw [← hx]; exact sourceK_canonical x
  have canonRho : Canonical p.rho := by
    obtain ⟨x,_,hx⟩ := flat.rho
    rw [← hx]; exact sourceK_canonical x
  exact ⟨NCI_QueryInvariant.accepted_bounds [] _ validated,
    NCI_QueryInvariant.accepted_unique [] _ validated,lengthWeights,canonWeights,canonPower,canonRho,
    CheckpointBytes4Ops.successful_reservation reserved D ck proof publicInput .S2 hash p a success,
    f,flat.finalCursor,flat.powerCursor⟩
#print axioms sourceK_canonical
#print axioms returned_domains
end AspisR1.NCI_ResumeDomains
