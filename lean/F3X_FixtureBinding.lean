import S2W_AuthenticatedInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_FixtureBinding
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem proof_public (H : Bytes → State) (proof1 pub1 proof2 pub2 : Slice U8)
    (proof : bytesOf proof2.val=bytesOf proof1.val)
    (pub : bytesOf pub2.val=bytesOf pub1.val) :
    S2W_AuthenticatedInputs.P2Prime H proof1 pub1 proof2 pub2 := by
  exact ⟨fun _=>⟨proof,pub⟩⟩

#print axioms proof_public
end AspisR1.F3X_FixtureBinding
end
