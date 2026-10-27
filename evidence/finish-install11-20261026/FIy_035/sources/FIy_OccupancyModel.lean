import FIy_OccupancyMeaning
import R0P.Occupancy
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyModel
open Aeneas Aeneas.Std
open FIv_NativeValue (K)

theorem value (input output : K) (expected : Nat) (a : Nat → K) :
    List.ofFn (FIy_OccupancyMeaning.model input output expected a)=
      R0P.occupancyLanesLiteral input output (expected : K) (fun i=>a i.val) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,R0P.occupancyLanesLiteral,List.length_append,
      List.length_cons,List.length_nil,List.length_ofFn]
    rfl
  · intro j hj _
    have bound : j<12 := by
      have h : j<(12#usize).val := by simpa only [List.length_ofFn] using hj
      exact h
    rw [List.getElem_ofFn]
    by_cases h0 : j=0
    · subst j
      simp [FIy_OccupancyMeaning.model,FIy_OccupancyPrefix.model,R0P.occupancyLanesLiteral,Function.update]
    · by_cases h1 : j=1
      · subst j
        simp [FIy_OccupancyMeaning.model,FIy_OccupancyPrefix.model,R0P.occupancyLanesLiteral,Function.update]
      · by_cases h2 : j=2
        · subst j
          simp [FIy_OccupancyMeaning.model,FIy_OccupancyPrefix.model,R0P.occupancyLanesLiteral,Function.update]
        · by_cases h11 : j=11
          · subst j
            simp only [FIy_OccupancyMeaning.model,h11,↓reduceIte,lower,upper,and_self,
              R0P.occupancyLanesLiteral,List.getElem_append,List.length_append,List.length_cons,List.length_nil,
              List.length_ofFn,Nat.reduceAdd,show ¬j<3 by omega,show j<11 by omega,
              ↓reduceDIte,List.getElem_ofFn]
            congr 3
            omega
#print axioms value
end AspisR1.FIy_OccupancyModel
end
