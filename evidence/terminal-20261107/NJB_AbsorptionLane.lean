import NJB_AbsorptionScales
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_AbsorptionLane
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJB_AbsorptionScales (Scale)
def group (lane : Fin 16) : Fin 3 :=
 if lane.val<2 then 0 else if lane.val<8 then 1 else 2
def reference (scales : Fin 3 → Scale) (opened : Fin 16 → NQ) (lane : Fin 16) : Result NQ :=
 FIq_Native.field.PreparedQm31Multiplier.mul (scales (group lane)).cache (opened lane)
theorem result (scales : Fin 3 → Scale) (opened : Fin 16 → NQ) (lane : Fin 16)
 (prepared : ∀ i,Canon (scales i).value ∧ NJB_PreparedLaws.Domain (scales i).cache (scales i).value)
 (canonical : ∀ i,Canon (opened i)) :
 ∃ out,reference scales opened lane=ok out ∧ Canon out ∧
 decode out=decode (scales (group lane)).value*decode (opened lane) :=
 NJB_PreparedLaws.mul_result (scales (group lane)).cache (scales (group lane)).value (opened lane)
  (prepared _).1 (canonical _) (prepared _).2
/-- The complete returned field value agrees with the retained literal
low*blocks*opened formula for each of the three actual source branches. -/
def literal (low fixed two eight nodes opened : K) (lane : Fin 16) : K :=
 let blocks := if lane.val<2 then fixed else if lane.val<8 then fixed+two else fixed+two+eight+nodes
 low*blocks*opened
theorem model_eq_literal (low fixed two eight nodes opened : K) (lane : Fin 16) :
 NJB_AbsorptionScales.model low fixed two eight nodes (group lane)*opened=
 literal low fixed two eight nodes opened lane := by
 by_cases first : lane.val<2
 · simp [group,literal,NJB_AbsorptionScales.model,first]
 · by_cases second : lane.val<8
   · simp [group,literal,NJB_AbsorptionScales.model,first,second]
   · simp [group,literal,NJB_AbsorptionScales.model,first,second]
#print axioms result
#print axioms model_eq_literal
end AspisR1.NJB_AbsorptionLane
end
