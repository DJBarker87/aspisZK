import FJa_ExpandValue
import FJa_TensorMeaning
import FJa_Seed
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ExpansionMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
/-- Literal point tensor computed by the ORIGINAL installed expand body,
with its actual seed and successful coordinate operations. -/
theorem value (N : Usize) (coordinates : Slice NQ) (out : Array NQ N)
    (hc : ∀ x∈coordinates.val,Canon x) (hsize : N.val=2^coordinates.val.length)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.expand N coordinates=ok out)
    (j : Fin N.val) :
    FIv_NativeArray.value out j.val=FJa_TensorMeaning.weight (coordinates.val.map decode) j.val := by
  unfold pool_v1.pair_forest_copy_terminal.Selectors.expand at run
  obtain ⟨seed,hs,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨iterator,hi,run⟩ := FIv_Map.bind_success _ _ _ run
  have seedFacts := FJa_Seed.value seed hs
  have same : iterator=⟨coordinates,0⟩ := (Result.ok.inj hi).symm
  rw [same] at run
  have v := FJa_ExpandValue.loop _ seed out 1#usize hc seedFacts.1 run
  simp only [List.drop_zero,show (1#usize).val=1 from rfl] at v
  rw [congrFun v j.val,FJa_TensorMeaning.value _ 1 _ j.val (by
    simpa only [List.length_map,Nat.mul_one,←hsize] using j.isLt)]
  have ancestor : j.val/2^(coordinates.val.map decode).length=0 := by
    rw [List.length_map,←hsize]
    exact Nat.div_eq_of_lt j.isLt
  rw [ancestor,seedFacts.2,one_mul]
#print axioms value
end AspisR1.FJa_ExpansionMeaning
end
