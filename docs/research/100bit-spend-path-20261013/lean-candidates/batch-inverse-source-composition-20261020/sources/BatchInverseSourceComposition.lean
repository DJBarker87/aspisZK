import BatchBackwardEntrypoint
import BatchPrefixEntrypointModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

/-- Composition candidate of the checked indexed prefix cut and exact backward
cut. This is not the frozen whole QueryGeometry caller. -/
def runCandidate (flat : Vec U32) : Result (Vec U32) := do
  let (pref,product) ← AspisR1BatchPrefix.prefix_product currentMul flat
  backward currentMul currentInv flat pref product

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem runCandidate_success_inverses (flat out : Vec U32)
    (hnonzero : ∀ x ∈ flat.val, decode x ≠ 0)
    (h : runCandidate flat = .ok out) :
    out.val.map decode = (flat.val.map decode).map Inv.inv := by
  unfold runCandidate at h
  rcases bind_ok_inv h with ⟨pair,hprefix,hback⟩
  rcases pair with ⟨pref,product⟩
  have hmodel := AspisR1BatchPrefix.Proof.prefix_product_success_model flat (pref,product) hprefix
  have hplen : pref.val.length = flat.val.length := by
    have hlen := congrArg List.length hmodel.1
    simpa only [List.length_map,R1ZBatchInverseSourceModelV1.prefixRun_length] using hlen
  have hp : ∀ (j : Nat) (hj : j < flat.val.length) (hp : j < pref.val.length),
      decode (pref.val[j]'hp) = ((flat.val.map decode).take j).prod := by
    intro j hj hpj
    have hv := AspisR1BatchPrefix.Proof.prefix_product_success_recorded flat (pref,product) hprefix j hj
    simpa [hpj] using hv
  have hs := backward_success_inverses flat pref product out (Nat.le_of_eq hplen.symm) hp hmodel.2 hnonzero hback
  apply List.ext_getElem
  · simpa only [List.length_map] using hs.1
  · intro i hout hflat
    have hi : i < flat.val.length := by simpa only [List.length_map] using hflat
    have ho : i < out.val.length := by simpa only [List.length_map] using hout
    have hv := hs.2 i hi
    simpa only [List.getElem_map,atM_get out i ho,atM_get flat i hi] using hv

#print axioms runCandidate_success_inverses
end AspisR1BatchBackward.Proof
