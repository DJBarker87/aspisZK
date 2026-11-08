import NMV_ConcreteWindows
import NVR_G2Reference
import TAS_Interfaces
-- NVR_ provenance: copied from evidence/stage-wrap-20261111/NMV_TasRoots.lean (research, sha256 6595a2baf5d394d3...).
-- Change: NMV_ -> NVR_ renames of the rev4-repaired chain modules only; no proof edit.
set_option autoImplicit false
namespace NVR_TasRoots
open RSL

/-- SAME child constants as the top's Impl; only the two owned wrapper
fields are installed with the full-carrier source-fission interpreter.
Native association remains OPEN under NMV-CONTROL-1; no source root is asserted. -/
def implementation {L : PoolLib} {V0 : TX2_241.V2Lib} {VL : VLib}
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) : TAS.Impl L V0 VL :=
 { I with f344 := NMV_ConcreteWindows.stage1 a1 I.f345,
          f240 := NMV_ConcreteWindows.stage2 a2 I.f241 }

theorem children_same {L : PoolLib} {V0 : TX2_241.V2Lib} {VL : VLib}
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) :
 (implementation I a1 a2).f241=I.f241 ∧ (implementation I a1 a2).f345=I.f345 := ⟨rfl,rfl⟩

/-- Exact TAS r240 field: EVERY V2Lib, full241 at the SAME constant. -/
theorem field240 (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib) (VL : VLib)
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) :
 ∀ V : TX2_241.V2Lib,
 TX2_241.RowSpec_241 L D V (implementation I a1 a2).f241 →
 TX2_240.RowSpec_240 L D V (implementation I a1 a2).f240 :=
 fun V child => NMV_ConcreteWindows.root240 L D V a2 I.f241 child

/-- Exact TAS r344 field, retaining complete child effects and checkpoints. -/
theorem field344 (L : PoolLib) (V0 : TX2_241.V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation) :
 TX1_345.RowSpec_345 VL P C (implementation I a1 a2).f345 →
 TX1_344.RowSpec_344 VL P C (implementation I a1 a2).f344 :=
 fun child => NMV_ConcreteWindows.root344 VL P C a1 I.f345 child

/-- Exact three-field TAS package. PoolLaws is a CLOSED-library installation
obligation, not a wrapper own-input clause or a new trust item. No such law
is inferred for an unconstrained PoolLib. -/
def packet (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation)
 (pl : NMV_NoWrite.PoolLaws L) :
 TAS.NMV_Roots L D V0 VL P C (implementation I a1 a2) where
 r240 := field240 L D V0 VL I a1 a2
 r344 := field344 L V0 VL P C I a1 a2
 g2 := fun law hw a s env o h => NVR_G2Reference.frame L D V0 pl law hw a s env o h

/-- Installed weak240 instance, with NO Root0 or selection hypothesis. -/
theorem weak240 (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib) (VL : VLib)
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation)
 (law : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (child : TX2_241.RowSpec_241 L D (TCK.weaken V0 law) I.f241)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TX2_240.Ref L D (TCK.weaken V0 law) a s env ((implementation I a1 a2).f240 a s env) :=
 field240 L D V0 VL I a1 a2 (TCK.weaken V0 law) child a s env (TCK.domain240_weaken V0 law a s)

theorem weakFrame (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib) (VL : VLib)
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation)
 (pl : NMV_NoWrite.PoolLaws L)
 (law : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (hw : ∀ p q r, TAS.WriteFree (law p q r))
 (child : TX2_241.RowSpec_241 L D (TCK.weaken V0 law) I.f241)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TAS.Frame s ((implementation I a1 a2).f240 a s env) :=
 NVR_G2Reference.frame L D V0 pl law hw a s env _ (weak240 L D V0 VL I a1 a2 law child a s env)

#print axioms children_same
#print axioms field240
#print axioms field344
#print axioms packet
#print axioms weak240
#print axioms weakFrame
end NVR_TasRoots
