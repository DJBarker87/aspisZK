import NCL_DriverCuts
import DrvC_FirstPure
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_ShapeDomain
open Aeneas Aeneas.Std Result DrvC_Installation

/-- The same installed parse result determines S2 and the full57607 proof
length used by every TX1 lower caller. This is an installed-model domain law. -/
theorem source {F C : Type} (c : Configuration F C)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (saved : alloc.vec.Vec U8)
    (cut : NCL_DriverCuts.Cuts (currentInstalled c) (currentDigest c) semantic pub proof () saved) :
    cut.parsed=.S2 ∧ proof.val.length=57607 ∧
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf proof.val)=true := by
  have call : Op3I_Install.sourceBody proof=ok (.Ok cut.parsed) := cut.shape
  obtain ⟨variant,header⟩ := Op3I_Install.header_of_success proof cut.parsed call
  refine ⟨variant,?_,header⟩
  simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using
    ((OraclePortHeader.accepts_iff _).mp header).1
#print axioms source
end AspisR1.NCL_ShapeDomain
end
