import NMV_RslFold
import NMV_WeakFold
import NMV_PhysicalCarrier
import NMV_Stage1Frame
import NVR_CandidateRoots
import NVR_TAS
-- Focused combined import of the locally compilable rev4 repair (core Lean only).
-- Not imported here because they need Aeneas: NVR_NNCWeak, NVR_Carrier,
-- NVR_DispatchEmitted, NVR_Reify.
set_option autoImplicit false
noncomputable section
namespace NVR_Combined
open RSL

/-- The dispatcher install over the wrapper install, as TGA residual item 2
requires. Both NMV and NMW root packets inhabit the SAME composed Impl. This
is a coherence check only; it closes no row and installs no concrete Impl. -/
def composed {L : PoolLib} {V0 : TX2_241.V2Lib} {VL : VLib}
    (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) : TAS.Impl L V0 VL :=
  NVR_TAS.install (NVR_TasRoots.implementation I a1 a2)

def composed_nmv (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : TX1_345.S1Lib VL) (I : TAS.Impl L V0 VL)
    (a1 a2 : NMV_ConcreteWindows.Allocation) (pl : NMV_NoWrite.PoolLaws L) :
    TAS.NMV_Roots L D V0 VL P C (composed I a1 a2) :=
  let p := NVR_TasRoots.packet L D V0 VL P C I a1 a2 pl
  ⟨p.r240, p.r344, p.g2⟩

theorem composed_nmw (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : TX1_345.S1Lib VL) (I : TAS.Impl L V0 VL)
    (a1 a2 : NMV_ConcreteWindows.Allocation) :
    TAS.NMW_Roots (L := L) (D := D) (V0 := V0) (VL := VL) (P := P) (C := C)
      (I := composed I a1 a2) :=
  NVR_TAS.roots L D V0 VL P C (NVR_TasRoots.implementation I a1 a2)

end NVR_Combined
#check @NMV_RslFold.fold344
#check @NMV_RslFold.fold240
#check @NMV_WeakFold.fold240
#check @NVR_CandidateRoots.root344
#check @NVR_CandidateRoots.root240
#check @NVR_TasRoots.field344
#check @NVR_Folds.process_tx1
#check @NVR_Folds.process_tx2
#check @NVR_Folds.entry_tx1
#check @NVR_Folds.entry_tx2
#print axioms NMV_RslFold.fold344
#print axioms NMV_RslFold.fold240
#print axioms NMV_WeakFold.fold240
#print axioms NVR_TasRoots.field344
#print axioms NVR_TasRoots.field240
#print axioms NVR_TasRoots.packet
#print axioms NVR_CandidateRoots.root344
#print axioms NVR_CandidateRoots.root240
#print axioms NVR_CandidateRoots.packet
#print axioms NVR_Folds.process_tx1
#print axioms NVR_Folds.process_tx2
#print axioms NVR_Folds.entry_tx1
#print axioms NVR_Folds.entry_tx2
#print axioms NVR_TAS.roots
#print axioms NVR_TAS.weak_entry
#print axioms NVR_Combined.composed_nmv
#print axioms NVR_Combined.composed_nmw
