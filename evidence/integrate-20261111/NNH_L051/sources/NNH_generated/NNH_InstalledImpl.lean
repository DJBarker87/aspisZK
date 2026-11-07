import NNH_CandidateRoots
import NNF_TAS
set_option autoImplicit false
namespace NNH_InstalledImpl
open RSL
open RSL.TX2_241 (V2Lib)
open RSL.TX1_345 (S1Lib)

/-- The sole wrapper/dispatcher installation. This leaves every child at the
supplied I0 constant; it does not claim I0 has its missing native producer. -/
def install {L : PoolLib} {V0 : V2Lib} {VL : VLib}
 (I0 : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) : TAS.Impl L V0 VL :=
 NNF_TAS.install (NNH_TasRoots.implementation I0 a1 a2)

theorem wrappers {L : PoolLib} {V0 : V2Lib} {VL : VLib}
 (I0 : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) :
 (install I0 a1 a2).f344 = NMV_ConcreteWindows.stage1 a1 I0.f345 ∧
 (install I0 a1 a2).f240 = NMV_ConcreteWindows.stage2 a2 I0.f241 := ⟨rfl,rfl⟩

theorem children {L : PoolLib} {V0 : V2Lib} {VL : VLib}
 (I0 : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) :
 (install I0 a1 a2).f217=I0.f217 ∧ (install I0 a1 a2).f234=I0.f234 ∧
 (install I0 a1 a2).f233=I0.f233 ∧ (install I0 a1 a2).f242=I0.f242 ∧
 (install I0 a1 a2).f064=I0.f064 ∧ (install I0 a1 a2).f241=I0.f241 ∧
 (install I0 a1 a2).f136=I0.f136 ∧ (install I0 a1 a2).f137=I0.f137 ∧
 (install I0 a1 a2).f087=I0.f087 ∧ (install I0 a1 a2).f094=I0.f094 ∧
 (install I0 a1 a2).f328=I0.f328 ∧ (install I0 a1 a2).f345=I0.f345 :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem dispatch (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : S1Lib VL) (I0 : TAS.Impl L V0 VL)
 (a1 a2 : NMV_ConcreteWindows.Allocation) :
 TAS.NMW_Roots L D V0 VL P C (install I0 a1 a2) :=
 NNF_TAS.roots L D V0 VL P C (NNH_TasRoots.implementation I0 a1 a2)

theorem stages (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : S1Lib VL) (I0 : TAS.Impl L V0 VL)
 (a1 a2 : NMV_ConcreteWindows.Allocation) (pl : NMV_NoWrite.PoolLaws L) :
 TAS.NMV_Roots L D V0 VL P C (install I0 a1 a2) :=
 NNH_CandidateRoots.packet L D V0 VL P C I0 a1 a2 pl

#print axioms wrappers
#print axioms children
#print axioms dispatch
#print axioms stages
end NNH_InstalledImpl
