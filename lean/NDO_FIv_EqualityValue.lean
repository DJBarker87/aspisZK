import NDO_FIv_EqualityReach
import NDO_FIv_EqualityShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_EqualityValue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIv_NativeArray (value)
def weight (left right : Array NQ 10#usize) : K := FIv_EqualityLoop.tail left right 0 10

theorem exact_value (left right : Array NQ 10#usize)
    (hl : ∀ x∈left.val,Canon x) (hr : ∀ x∈right.val,Canon x) (out : NQ)
    (run : FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value left right=ok out) :
    Canon out ∧ decode out=weight left right := by
  obtain ⟨a,b,product,ha,hb,hp,run⟩ := FIv_EqualityReach.reached left right out run
  have va := FIv_NativeArray.canonical left 0#usize a hl ha
  have vb := FIv_NativeArray.canonical right 0#usize b hr hb
  have vp := FIv_EqualityCell.value a b product va vb hp
  have rest := FIv_EqualityLoop.exact_loop left right hl hr 9 1#usize product out (by decide) vp.1 run
  refine ⟨rest.1,?_⟩
  rw [rest.2,vp.2,← FIv_NativeArray.read left 0#usize a ha,← FIv_NativeArray.read right 0#usize b hb]
  have shape := FIv_EqualityShape.step left right 0 9
  simpa only [weight,show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,Nat.zero_add] using shape.symm

#print axioms exact_value
end AspisR1.FIv_EqualityValue
end
