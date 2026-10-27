import JGg_ScalarForward
import JGg_Opening27
import JFq_Gamma
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_GammaSample
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

/-- Bounded scalar cell:32 literal bytes,8 base-p digits,one small carry and
8-coordinate decode. No SHA recurrence or finite-field universe is reduced. -/
theorem sample : candidateGammaPublic (encodeState JGg_Opening27.block0)=ok value := by
  rfl
#print axioms sample
end AspisR1.JGy_GammaSample
end
