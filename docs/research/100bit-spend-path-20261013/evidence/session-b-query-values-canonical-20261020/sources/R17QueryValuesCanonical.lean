import R17QueryValuesWholeBodyStoredV1
import R17CurrentDomainCanonical
import M31InverseCanonicalBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R17QueryValuesCanonical
open AspisR1QueryGeometryActual R17QueryPerItemValuesV2 R17CurrentDomainCanonical
open R17QueryValuesWholeBodyV21 R17QueryValuesWholeBodyStoredV1

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem perQueryCore_canonical (u ix iy : domain.FibreIndex)
    (point : domain.Point field.M31) (x y z : field.M31)
    (h : perQueryCore actualCMOps actualM31Ops u ix iy = .ok (point,x,y,z)) :
    CanonicalM point.x ∧ CanonicalM point.y ∧ CanonicalM x ∧ CanonicalM y ∧ CanonicalM z := by
  unfold perQueryCore at h
  rcases bind_ok_inv h with ⟨pt,hpt,h⟩
  rcases bind_ok_inv h with ⟨x1,hx,h⟩
  rcases bind_ok_inv h with ⟨y1,hy,h⟩
  rcases bind_ok_inv h with ⟨xx,hxx,h⟩
  rcases bind_ok_inv h with ⟨twice,ht,h⟩
  rcases bind_ok_inv h with ⟨z1,hz,h⟩
  have he : (pt,x1,y1,z1)=(point,x,y,z) := Result.ok.inj h
  cases he
  have hpc := fibre_point_success_canonical u point hpt
  have hxc := line_node_success_canonical ix x hx
  have hyc := line_node_success_canonical iy y hy
  have hxxc := mul_success_canonical x x xx hxx
  have htc := double_success_canonical xx twice hxxc ht
  have hzc := sub_success_canonical twice (1#u32) z htc (by change (1:Nat)<2147483647; decide) hz
  exact ⟨hpc.1,hpc.2,hxc,hyc,hzc⟩

theorem emittedRaw_success_canonical
    (q : U32)
    (anyCheck : core.slice.iter.Iter field.M31 → Result (Bool × core.slice.iter.Iter field.M31))
    (arr : Array field.M31 5#usize) (z : field.M31)
    (h : emittedRawWithCallees actualSourceCallees anyCheck q = .ok (.Ok (arr,z))) :
    (∀ x ∈ arr.val, CanonicalM x) ∧ CanonicalM z := by
  have he := emittedRawWithCallees_eq_directWithCallees actualSourceCallees q anyCheck
  have hd : directWithCallees actualSourceCallees q anyCheck = .ok (.Ok (arr,z)) := he.symm ▸ h
  rw [direct_eq_queryValuesEntry q anyCheck] at hd
  obtain ⟨u,ix,iy,point,x,y,_,_,_,_,_,hcore,harr,_⟩ :=
    R17QueryValuesEntryActualV1.successful_queryValuesEntry_core q anyCheck arr z hd
  have hc := perQueryCore_canonical u ix iy point x y z hcore
  constructor
  · rw [harr]
    change ∀ v ∈ [point.x,point.y,x,y,z],CanonicalM v
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with h | h | h | h | h <;> subst v
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2.1
    · exact hc.2.2.2.2
  · exact hc.2.2.2.2

theorem emittedRaw_success_nonzero_decode
    (q : U32)
    (anyCheck : core.slice.iter.Iter field.M31 → Result (Bool × core.slice.iter.Iter field.M31))
    (arr : Array field.M31 5#usize) (z : field.M31)
    (h : emittedRawWithCallees actualSourceCallees anyCheck q = .ok (.Ok (arr,z)))
    (hn : ∀ x ∈ arr.val, x ≠ 0#u32) :
    ∀ x ∈ arr.val, R17CurrentM31Semantics.decode x ≠ 0 := by
  have hc := emittedRaw_success_canonical q anyCheck arr z h
  intro x hx
  exact (AspisR1M31Inverse.SquareProof.canonical_word_nonzero_iff x (hc.1 x hx)).mp (hn x hx)

#print axioms perQueryCore_canonical
#print axioms emittedRaw_success_canonical
#print axioms emittedRaw_success_nonzero_decode
end R17QueryValuesCanonical
