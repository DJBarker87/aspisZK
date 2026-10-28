import NDO_JGg_ScalarForward
import NDO_JGg_Opening27
import RPt_JFq_Gamma
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_GammaSample
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge AspisV8R19.SqueezeOracleBridge

/-- The eight retained checkpoint limbs, in the public preparation carrier. -/
def value : AspisR1PublicPreparation.aspis_core.field.WideExact :=
  ⟨⟨⟨855639275#u32,1483149559#u32⟩,⟨1898717401#u32,1849775942#u32⟩⟩,
    ⟨⟨1112406525#u32,1796814865#u32⟩,⟨1838939499#u32,418714188#u32⟩⟩⟩

def stage (x : AspisR1PublicPreparation.aspis_core.field.WideExact) :
    AspisR1Stage2.aspis_core.field.wide_exact.WideExact :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem checkpoint : stage value=JFq_Gamma.scalar := rfl
#print axioms checkpoint

def digits : AspisR1GammaCaller.DigitsModel.GammaDigits :=
  Array.make 8#usize [855639275#u32,1483149559#u32,1898717401#u32,1849775942#u32,
    1112406525#u32,1796814865#u32,1838939499#u32,418714188#u32]

def nativeValue : AspisR1GammaCaller.DigitsModel.GammaWide :=
  ⟨⟨⟨855639275#u32,1483149559#u32⟩,⟨1898717401#u32,1849775942#u32⟩⟩,
    ⟨⟨1112406525#u32,1796814865#u32⟩,⟨1838939499#u32,418714188#u32⟩⟩⟩

theorem digits_injective : Function.Injective AspisR1GammaCaller.DigitsModel.values := by
  have injective : Function.Injective (List.map (fun x : U32 => x.val)) := by
    intro xs
    induction xs with
    | nil =>
      intro ys eq
      cases ys with
      | nil => rfl
      | cons y ys => cases eq
    | cons x xs ih =>
      intro ys eq
      cases ys with
      | nil => cases eq
      | cons y ys =>
        have parts := List.cons.inj eq
        have head : x=y := UScalar.eq_of_val_eq parts.1
        have tail : xs=ys := ih parts.2
        cases head
        cases tail
        rfl
  intro a b eq
  apply Subtype.ext
  exact injective eq
#print axioms digits_injective

/-- Rank is reduced through its eight-word closed form, never through a
function-space enumeration or the extracted low-digit loops. -/
theorem rank_value : AspisR1.SourceSamplerByteRank.rank (encodeState JGg_Opening27.block0) = 77433688320881852136176613328741332368108119866937330856405566397951541996177 := by
  rw [←AspisR1.SourceSamplerByteRank.word_value]
  with_unfolding_all rfl
#print axioms rank_value

theorem computed : AspisR1.SamplerNatModel.gammaDigits
    (AspisR1.SourceSamplerByteRank.rank (encodeState JGg_Opening27.block0)) =
    AspisR1GammaCaller.DigitsModel.values digits := by
  rw [rank_value]
  with_unfolding_all rfl
#print axioms computed

/-- Only the bounded eight-coordinate decoder is reduced. -/
theorem decoded : AspisR1GammaCaller.DigitsModel.candidateGammaHelpers.decode digits = ok nativeValue := by
  with_unfolding_all rfl
#print axioms decoded

theorem sample : candidateGammaPublic (encodeState JGg_Opening27.block0)=ok value := by
  let block := encodeState JGg_Opening27.block0
  obtain ⟨out,call⟩ := AspisR1GammaCaller.DigitsModel.candidate_gamma_total block
  have refinement : AspisR1GammaCaller.DigitsModel.HelpersRefine
      AspisR1GammaCaller.DigitsModel.candidateGammaHelpers :=
    AspisR1GammaCaller.DigitsModel.candidate_helpers_refine
      AspisR1GammaCaller.DigitsModel.candidateGammaHelpers.decode
  obtain ⟨ds,decode,values⟩ := AspisR1GammaCaller.DigitsModel.gamma_digits_success
    AspisR1GammaCaller.DigitsModel.candidateGammaHelpers refinement block out call
  have sameDigits : ds=digits := digits_injective (values.trans computed)
  subst ds
  have same : nativeValue=out := Result.ok.inj (decoded.symm.trans decode)
  rw [←same] at call
  unfold candidateGammaPublic
  rw [call,bind_tc_ok]
  rfl
#print axioms sample
end AspisR1.JHa_GammaSample
end
