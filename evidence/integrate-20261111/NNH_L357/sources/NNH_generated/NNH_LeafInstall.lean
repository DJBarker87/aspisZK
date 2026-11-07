import NNH_Libraries
import NNH_InstalledImpl
import NNG_Candidate136
import NMX_R3_DecoderFold
set_option autoImplicit false
noncomputable section
namespace NNH_LeafInstall
open RSL NNH_Libraries
/-- Published complete136/217 candidate producers. This installs their exact
mathematical functions; their native ledger gate remains external and pending.
No candidate is re-proved or given row credit by integration. -/
def install (I0 : TAS.Impl L V0 VL) (allocation217 : Bytes → Env → Bool) : TAS.Impl L V0 VL :=
 {I0 with f136 := AspisR1.NNG_Producer136.producer,
          f217 := NMX_R3_DecoderFold.decode allocation217}

theorem finish (I0 : TAS.Impl L V0 VL) (allocation217 : Bytes → Env → Bool)
 (alloc1 alloc2 : NMV_ConcreteWindows.Allocation) :
 TAS.NMO_Root L V0 VL (NNH_InstalledImpl.install (install I0 allocation217) alloc1 alloc2) :=
 ⟨AspisR1.NNG_Candidate136.candidate⟩

theorem lane (I0 : TAS.Impl L V0 VL) (allocation217 : Bytes → Env → Bool)
 (alloc1 alloc2 : NMV_ConcreteWindows.Allocation) :
 TX2_217.RowSpec_217 (NNH_InstalledImpl.install (install I0 allocation217) alloc1 alloc2).f217 :=
 NMX_R3_DecoderFold.root allocation217

theorem tx2 (I0 : TAS.Impl L V0 VL) (allocation217 : Bytes → Env → Bool)
 (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (registry : TX2_234.RowSpec_234 L D I0.f234) :
 TAS.NMM_Roots L D V0 VL (NNH_InstalledImpl.install (install I0 allocation217) alloc1 alloc2) :=
 ⟨lane I0 allocation217 alloc1 alloc2,registry⟩

#print axioms finish
#print axioms lane
#print axioms tx2
end NNH_LeafInstall
