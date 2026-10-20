import BatchBackwardStepSemantics
import R1ZBatchInverseAlgebraV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec R1ZBatchInverseAlgebraV3

theorem field_step_inverse (flat pref : Vec U32) (suffix written suffix1 : U32)
    (n j : Nat) (hj : j < flat.val.length) (hjp : j < pref.val.length)
    (hn : n = j+1)
    (hsuffix : decode suffix = ((flat.val.map decode).take n).prod⁻¹)
    (hprefix : decode (pref.val[j]'hjp) = ((flat.val.map decode).take j).prod)
    (hnonzero : ∀ x ∈ flat.val, decode x ≠ 0)
    (hw : decode written = decode suffix * decode (pref.val[j]'hjp))
    (hs : decode suffix1 = decode suffix * decode (flat.val[j]'hj)) :
    decode written = (decode (flat.val[j]'hj))⁻¹ ∧
    decode suffix1 = ((flat.val.map decode).take j).prod⁻¹ := by
  have hx : decode (flat.val[j]'hj) ≠ 0 := hnonzero _ (List.getElem_mem hj)
  have hp : ((flat.val.map decode).take j).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    have hm := List.mem_of_mem_take hz
    rcases List.mem_map.mp hm with ⟨a,ha,he⟩
    exact hnonzero a ha he
  have hprod : ((flat.val.map decode).take n).prod =
      ((flat.val.map decode).take j).prod * decode (flat.val[j]'hj) := by
    rw [hn,list_take_succ_prod (flat.val.map decode) j (by simpa only [List.length_map] using hj)]
    rw [List.getElem_map]
  rw [hprod] at hsuffix
  constructor
  · rw [hw,hsuffix,hprefix]
    exact inv_product_mul_left_cancel _ _ hp hx
  · rw [hs,hsuffix]
    exact inv_product_update _ _ hp hx

#print axioms field_step_inverse
end AspisR1BatchBackward.Proof
