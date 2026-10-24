import S1FinishChildrenV1
import S1ExtractedRoundChildrenTotalV1
set_option autoImplicit false
namespace AspisS1FinishChildren
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23

def decodeQ (q : MainQM) :=
  AspisR1.ExtractedMaskQM31Exact.decode (genQToProbe (mainToGen q))

/-- TOTAL on canonical inputs for the concrete finish add; no assumed
successful field call. This is not unrestricted raw-word totality. -/
theorem add_total (x y : MainQM) (hx : Canonical x) (hy : Canonical y) :
    ∃ out, add x y = ok out ∧ Canonical out ∧ decodeQ out = decodeQ x + decodeQ y := by
  obtain ⟨out,call,canon,value⟩ := generated_qm_add_exact (mainToGen x) (mainToGen y) hx hy
  refine ⟨genToMain out,?_,?_,?_⟩
  · simp only [add,call,genResultToMain]
  · cases out with
    | mk c0 c1 => cases c0; cases c1; exact canon
  · cases out with
    | mk c0 c1 => cases c0; cases c1; exact value

theorem mul_total (x y : MainQM) (hx : Canonical x) (hy : Canonical y) :
    ∃ out, mul x y = ok out ∧ Canonical out ∧ decodeQ out = decodeQ x * decodeQ y := by
  obtain ⟨out,call,canon,value⟩ := generated_qm_mul_exact (mainToGen x) (mainToGen y) hx hy
  refine ⟨genToMain out,?_,?_,?_⟩
  · simp only [mul,call,genResultToMain]
  · cases out with
    | mk c0 c1 => cases c0; cases c1; exact canon
  · cases out with
    | mk c0 c1 => cases c0; cases c1; exact value

/-- Exact final arithmetic call sequence used by FinishModel.finish. The
producer domains remain explicit until their concrete source joins land. -/
theorem masked_terminal_total (mask eta terminal extra : MainQM)
    (hm : Canonical mask) (he : Canonical eta)
    (ht : Canonical terminal) (hx : Canonical extra) :
    ∃ out,
      (do let product ← mul eta terminal
          let sum ← add mask product
          add sum extra) = ok out ∧
      Canonical out ∧ decodeQ out = decodeQ mask + decodeQ eta * decodeQ terminal + decodeQ extra := by
  obtain ⟨product,productCall,productCanon,productValue⟩ := mul_total eta terminal he ht
  obtain ⟨sum,sumCall,sumCanon,sumValue⟩ := add_total mask product hm productCanon
  obtain ⟨out,outCall,outCanon,outValue⟩ := add_total sum extra sumCanon hx
  refine ⟨out,?_,outCanon,?_⟩
  · rw [productCall,bind_tc_ok,sumCall,bind_tc_ok,outCall]
  · rw [outValue,sumValue,productValue]

#print axioms add_total
#print axioms mul_total
#print axioms masked_terminal_total
end AspisS1FinishChildren
