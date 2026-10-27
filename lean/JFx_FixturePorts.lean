import JFx_NativeBytes
import CPhy_Ranges
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_FixturePorts
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open JFx_NativeBytes

/-- P2Prime is inhabited at the retained pair's equal proof/public byte
carriers. No global hash injectivity assumption is needed for these values. -/
theorem same_inputs (H : Bytes → State) :
    S2W_AuthenticatedInputs.P2Prime H proof publicInput proof publicInput :=
  ⟨fun _ => ⟨rfl,rfl⟩⟩

/-- All six checked node ranges and the compact y1 argument use the SAME
retained proof carrier. This does not assert its scan or parser acceptance. -/
theorem physical_ranges :
    S2W_ChildJoins.MultiproofConeJoin proof proof (CPhy_Ranges.nodes proof proof) ∧
    S2W_ChildJoins.S8StageConeJoin proof (CPhy_Ranges.y1 proof) := by
  refine ⟨CPhy_Ranges.multiproof proof proof proofBytes_length proofBytes_length,⟨⟨?_,?_⟩⟩⟩
  · change 7495 ≤ proofBytes.length
    rw [proofBytes_length]
    decide
  · exact MultiproofConeSlices.range_total proof 7031#usize 7495#usize (by decide)
      (by change 7495 ≤ proofBytes.length; rw [proofBytes_length]; decide)

#print axioms same_inputs
#print axioms physical_ranges
end AspisR1.JFx_FixturePorts
end
