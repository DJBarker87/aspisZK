import NNG_Representation136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ProjectionFallback137
open Aeneas Aeneas.Std Result NNG_Transport NNG_DProjection136 NNG_LIBArrays
open NNG_Representation136

/-- Four zero limbs: a small closed carrier witness, not field evaluation. -/
def zero : LIB_VCarriers.QM31 := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> change (0 : Nat)<2147483647 <;> decide⟩

def representation (fallback : LIB_VCarriers.QM31) : Representation VL Unit where
  transcript := toT10
  challenges := projectChallenges fallback
  q := NNG_LIBScalar.project fallback
  alpha := projectArray fallback
  claims := projectClaims fallback
  k29 := projectArray fallback
  point := toT2
  record := toT14
  error := toT13
  bytes := LIB_Carriers.bytes
  b32 := LIB_Carriers.b32
  qDom := NNG_LIBScalar.Domain
  q_injective := NNG_LIBScalar.injective_on fallback
  point_injective := NNG_LIBData.point_injective
  publicError := rfl
  terminalError := rfl
  equalError := rfl
  at28 := NNG_LIBArrays.at28 fallback
  bytes_length := NNG_LIBData.bytes_length
  root_bytes := NNG_LIBData.root_bytes

theorem representation_eq (a : Args) : representation a.challenges.eta = project a := rfl
#print axioms representation_eq
end AspisR1.NNG_ProjectionFallback137
