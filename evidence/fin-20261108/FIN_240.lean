import NMX_R9_StageTwo
import NMV_ConcreteWindows
import LIB_FullInstances
/-
FIN_ TX2:240 stage2 (r1_pool_adapter_owned.rs::stage2), one-step instantiation.
Fold:   NMV_ConcreteWindows.root240 (source unchanged at RSL rev4 per TGA_ G1;
        identical to NVR_CandidateRoots.root240, which only re-exports it).
Child:  NMX_R9_StageTwo.root (TX2:241 candidate 536c77b6e6b), at its own
        implementation NMX_R9_StageTwo.stage2 choices.
Library: LIB_FullInstances.L / D / V0 (= LIBB_PoolLib.library,
        LIB_Deployed.deployed, LIBB_V2Star.library; NMX's L/D/V are the same abbrevs).
Both the 233 allocation choices and the 240 window allocation are universally
quantified: the row holds at every allocator interpretation. No hypothesis is
added; the statement is RowSpec_240 exactly, with its original Domain (D2').
-/
set_option autoImplicit false
noncomputable section
namespace FIN_240
open RSL

abbrev L := LIB_FullInstances.L
abbrev D := LIB_FullInstances.D
abbrev V := LIB_FullInstances.V0

/-- The stage2 producer: the source-fission windows around the EXACT 241 producer. -/
def producer (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) :
    TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState) :=
  NMV_ConcreteWindows.stage2 allocation (NMX_R9_StageTwo.stage2 choices)

theorem candidate (choices : NMX_R4_Authentication.Choices)
    (allocation : NMV_ConcreteWindows.Allocation) :
    TX2_240.RowSpec_240 L D V (producer choices allocation) :=
  NMV_ConcreteWindows.root240 L D V allocation
    (NMX_R9_StageTwo.stage2 choices) (NMX_R9_StageTwo.root choices)

#print axioms candidate
end FIN_240
end
