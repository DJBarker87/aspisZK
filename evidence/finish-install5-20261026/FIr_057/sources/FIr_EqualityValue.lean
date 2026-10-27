import FIr_EqualityReach
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_EqualityValue
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic (NQ)
open FIr_NativeValue (Canon decode K)
open FIr_NativeArray (value)
def weight (left right : Array NQ 10#usize) : K := FIr_EqualityLoop.tail left right 0 10

theorem exact_value (left right : Array NQ 10#usize)
    (hl : ∀ x∈left.val,Canon x) (hr : ∀ x∈right.val,Canon x) (out : NQ)
    (run : FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value left right=ok out) :
    Canon out ∧ decode out=weight left right := by
  obtain ⟨a,b,product,ha,hb,hp,run⟩ := FIr_EqualityReach.reached left right out run
  have va := FIr_NativeArray.canonical left 0#usize a hl ha
  have vb := FIr_NativeArray.canonical right 0#usize b hr hb
  have vp := FIr_EqualityCell.value a b product va vb hp
  have rest := FIr_EqualityLoop.exact_loop left right hl hr 9 1#usize product out (by decide) vp.1 run
  refine ⟨rest.1,?_⟩
  rw [rest.2,vp.2,← FIr_NativeArray.read left 0#usize a ha,← FIr_NativeArray.read right 0#usize b hb]
  rw [weight,FIr_EqualityLoop.tail]

#print axioms exact_value
end AspisR1.FIr_EqualityValue
end
