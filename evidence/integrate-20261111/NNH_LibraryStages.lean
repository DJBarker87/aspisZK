import NNH_Libraries
import LIBB_PoolNoWrite
import NNH_InstalledImpl
set_option autoImplicit false
noncomputable section
namespace NNH_LibraryStages
open RSL NNH_Libraries
/-- G2 and both stage folds at the delivered canonical libraries. All Pool
no-write laws are supplied by the concrete library, with no PoolLaws premise. -/
def stages (I0 : TAS.Impl L V0 VL)
 (alloc1 alloc2 : NMV_ConcreteWindows.Allocation) :
 TAS.NMV_Roots L D V0 VL P C (NNH_InstalledImpl.install I0 alloc1 alloc2) :=
 NNH_InstalledImpl.stages L D V0 VL P C I0 alloc1 alloc2 LIBB_PoolNoWrite.laws

#print axioms stages
end NNH_LibraryStages
