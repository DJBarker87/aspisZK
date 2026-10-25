import S1SourceMaskOpsV1
import S1ExtractedRoundChildrenTotalV1
import S1AcceptedProductCanonicalV1
set_option autoImplicit false
namespace AspisS1SourceFinalOps
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23
def add (x y : MainQM) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (mainToGen x) (mainToGen y))
def mul (x y : MainQM) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (mainToGen x) (mainToGen y))
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


/-- Source-generated normal-return multiplication is canonical even without
numeric input premises. This is ACCEPTED-ONLY, not arbitrary-input TOTAL. -/
theorem mul_success_canonical (x y out : MainQM) (h : mul x y=ok out) : Canonical out := by
  unfold mul at h
  cases called : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (mainToGen x) (mainToGen y) with
  | ok actual =>
    simp only [called,genResultToMain] at h
    have same : genToMain actual=out := Result.ok.inj h
    rw [←same]
    have canonical := AspisS1AcceptedProductCanonical.generated_mul_success_canonical _ _ _ called
    cases actual with
    | mk c0 c1 => cases c0; cases c1; exact canonical
  | fail error => simp only [called,genResultToMain] at h; cases h
  | div => simp only [called,genResultToMain] at h; cases h

/-- Only actual source add/mul are fixed. Other full finish operations retain
base's semantics. Mask/selector/root-copy installations commute with it. -/
def install (base : AspisR1PublicPreparation.FinishModel.Boundaries) :
    AspisR1PublicPreparation.FinishModel.Boundaries := {base with add:=add,mul:=mul}

theorem root_copy_commutes (base : AspisR1PublicPreparation.FinishModel.Boundaries) :
    AspisR1PublicPreparation.S1SemanticRootCopy.install (install base)=
      install (AspisR1PublicPreparation.S1SemanticRootCopy.install base) := rfl

theorem mask_commutes (base : AspisR1PublicPreparation.FinishModel.Boundaries) :
    AspisS1SourceMaskOps.install (install base)=install (AspisS1SourceMaskOps.install base) := rfl

#print axioms add_total
#print axioms mul_total
#print axioms masked_terminal_total
#print axioms mul_success_canonical
#print axioms root_copy_commutes
#print axioms mask_commutes
end AspisS1SourceFinalOps
