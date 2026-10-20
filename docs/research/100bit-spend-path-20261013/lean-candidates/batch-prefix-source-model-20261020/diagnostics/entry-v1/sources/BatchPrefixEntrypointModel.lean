import BatchPrefixLoopSemantics
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchPrefix.Proof
open R17CurrentM31Semantics
open alloc.vec R1ZBatchInverseSourceModelV1

theorem prefix_product_success_model (flat : Vec U32) (out : Vec U32 × U32)
    (h : prefix_product AspisR1Qm31ArithmeticProbe.field.M31.mul flat = .ok out) :
    out.1.val.map decode = prefixRun (flat.val.map decode) 1 ∧
    decode out.2 = (flat.val.map decode).prod := by
  have hone : decode field.M31.ONE = 1 := by rw [field.M31.ONE]; rfl
  have hi : (0#usize).val ≤ flat.val.length := Nat.zero_le _
  have hr := loop_success_model AspisR1Qm31ArithmeticProbe.field.M31.mul current_mul_decode
    flat (Vec.with_capacity U32 (Vec.len flat)) field.M31.ONE 0#usize out hi h
  simpa only [Vec.with_capacity,Vec.new,List.map_nil,List.nil_append,List.drop_zero,hone,one_mul] using hr

theorem prefix_product_success_recorded (flat : Vec U32) (out : Vec U32 × U32)
    (h : prefix_product AspisR1Qm31ArithmeticProbe.field.M31.mul flat = .ok out)
    (j : Nat) (hj : j < flat.val.length) :
    (out.1.val.map decode).getD j 1 = ((flat.val.map decode).take j).prod := by
  rw [(prefix_product_success_model flat out h).1]
  exact prefixRun_getD_eq_take_prod (flat.val.map decode) j (by simpa only [List.length_map] using hj)

theorem prefix_product_success_nonzero (flat : Vec U32) (out : Vec U32 × U32)
    (h : prefix_product AspisR1Qm31ArithmeticProbe.field.M31.mul flat = .ok out)
    (hn : ∀ x ∈ flat.val, decode x ≠ 0) : decode out.2 ≠ 0 := by
  rw [(prefix_product_success_model flat out h).2]
  apply List.prod_ne_zero
  intro x hx
  rcases List.mem_map.mp hx with ⟨a,ha,he⟩
  subst x
  exact hn a ha

#print axioms prefix_product_success_model
#print axioms prefix_product_success_recorded
#print axioms prefix_product_success_nonzero
end AspisR1BatchPrefix.Proof
