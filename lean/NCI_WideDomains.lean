import NCI_ResumeDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_WideDomains
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Ops CheckpointBytes4Layout CheckpointBytes4ReaderFields NCI_ResumeDomains

def WideCanonical (x : aspis_core.field.wide_exact.WideExact) : Prop :=
  Canonical x.c0 ∧ Canonical x.c1

theorem sourceE_canonical (x : OraclePortCheckpointAbiC5.E) : WideCanonical (sourceE x) := by
  change Canonical (sourceK x.re) ∧ Canonical (sourceK x.im)
  exact ⟨sourceK_canonical x.re,sourceK_canonical x.im⟩

theorem e_at (ck : Slice U8) (offset : Nat) (q : aspis_core.field.wide_exact.WideExact)
    (h : EAt ck offset q) : WideCanonical q := by
  obtain ⟨x,_,hx⟩ := h
  rw [←hx]
  exact sourceE_canonical x

theorem k_at (ck : Slice U8) (offset : Nat) (q : aspis_core.field.QM31)
    (h : KAt ck offset q) : Canonical q := by
  obtain ⟨x,_,hx⟩ := h
  rw [←hx]
  exact sourceK_canonical x

theorem resumed_wide (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (ck proof publicInput : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (size : ck.val.length=1768)
    (success : verifier.resumeWithOps (ops reserved) D ck proof publicInput .S2 hash=ok (.Ok (p,a))) :
    WideCanonical p.gamma ∧ WideCanonical p.kappa ∧ WideCanonical p.claim ∧ WideCanonical a.rhs ∧
    (∀ x ∈ p.alpha.val, WideCanonical x) ∧
    (∀ x ∈ p.semantic_alpha.val, Canonical x) := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof publicInput .S2 hash p a success
  have flat := flat_fields reserved ck p a f size
  refine ⟨e_at _ _ _ flat.gamma,e_at _ _ _ flat.kappa,e_at _ _ _ flat.claim,e_at _ _ _ flat.rhs,?_,?_⟩
  · rw [f.alpha]
    intro x hx
    change x ∈ [f.alpha0,f.alpha1] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact e_at _ _ _ flat.alpha0
    · exact e_at _ _ _ flat.alpha1
  · obtain ⟨model,_,contents⟩ := flat.semantic
    rw [contents]
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact sourceK_canonical y

theorem resumed_coordinates (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (ck proof publicInput : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (size : ck.val.length=1768)
    (success : verifier.resumeWithOps (ops reserved) D ck proof publicInput .S2 hash=ok (.Ok (p,a))) :
    ∀ z ∈ p.z.val, Canonical z.x ∧ Canonical z.y := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof publicInput .S2 hash p a success
  have flat := flat_fields reserved ck p a f size
  rw [f.coordinates]
  intro z hz
  change z ∈ [⟨f.x0,f.y0⟩,⟨f.x1,f.y1⟩] at hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl
  · exact ⟨k_at _ _ _ flat.x0,k_at _ _ _ flat.y0⟩
  · exact ⟨k_at _ _ _ flat.x1,k_at _ _ _ flat.y1⟩

#print axioms sourceE_canonical
#print axioms e_at
#print axioms k_at
#print axioms resumed_wide
#print axioms resumed_coordinates
end AspisR1.NCI_WideDomains
