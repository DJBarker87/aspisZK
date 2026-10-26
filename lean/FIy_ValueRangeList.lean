import FIy_ValueRangeShape
import R0P.Value
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ValueRangeList
open Aeneas Aeneas.Std
open FIy_ValueTail (Openings)

theorem value (o : Openings) :
    List.ofFn (FIy_ValueRangeShape.unweighted o)=R0P.valueRange (FIw_PublicModel.openings o) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,R0P.valueRange,List.length_append,List.length_ofFn,
      List.length_cons,List.length_nil]
    rfl
  · intro j hj _
    have bound : j<33 := by
      have h : j<(33#usize).val := by simpa only [List.length_ofFn] using hj
      exact h
    rw [List.getElem_ofFn,FIy_ValueRangeShape.value]
    by_cases h30 : j<30
    · have h32 : j≠32 := by omega
      have h31 : j≠31 := by omega
      have hEq30 : j≠30 := by omega
      simp only [h32,h31,hEq30,↓reduceIte,R0P.valueRange,List.getElem_append,
        List.length_append,List.length_ofFn,List.length_cons,List.length_nil,Nat.reduceAdd,
        h30,↓reduceDIte]
      by_cases h10 : j<10
      · have h20 : j<20 := by omega
        simp only [h10,h20,↓reduceDIte,↓reduceIte,List.getElem_ofFn,
          FIw_PublicModel.openings,FIx_ValueBitModel.bit,pow_two] <;> rfl
      · by_cases h20 : j<20
        · simp only [h10,h20,↓reduceDIte,↓reduceIte,List.getElem_ofFn,
            FIw_PublicModel.openings,FIx_ValueBitModel.bit,pow_two] <;> rfl
        · simp only [h10,h20,↓reduceDIte,↓reduceIte,List.getElem_ofFn,
            FIw_PublicModel.openings,FIx_ValueBitModel.bit,pow_two] <;> rfl
    · have lower : 30≤j := by omega
      interval_cases j <;>
        simp [R0P.valueRange,FIy_ValueTail.reconstruct,FIw_PublicModel.openings]
#print axioms value
end AspisR1.FIy_ValueRangeList
end
