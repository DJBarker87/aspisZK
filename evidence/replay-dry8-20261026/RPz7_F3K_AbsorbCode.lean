import RPz7_F3J_OpeningCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_AbsorbCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode

theorem run_absorb {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before absorbed : transcript.Transcript Hash) (payload : Slice U8)
    (success : transcript.Transcript.absorb D before 31#u8 payload=ok absorbed) :
    run (PreparedHashEffects.absorb effects D before 31#u8 payload)=
      ([Event.digest D before.hash (CallerStep.openingAbsorbParts before.state 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload) (ok absorbed.state)],ok absorbed) := by
  obtain ⟨tag,digestState,add,digest,absEq⟩ := PAln_OpeningCalls.absorb_success
    D before absorbed 31#u8 payload success
  change ok (191#u8)=ok tag at add
  cases Result.ok.inj add
  have tag_add : 160#u8+31#u8=ok (191#u8) := rfl
  rw [absEq]
  unfold CallerStep.openingAbsorbParts at digest ⊢
  simp only [PreparedHashEffects.absorb,Bind.bind,Pure.pure,PreparedHashCode.bind,run,lift,
    liftM,MonadLift.monadLift,MonadLiftT.monadLift,effects,tag_add,digest]

#print axioms run_absorb
end AspisR1.F3K_AbsorbCode
end
