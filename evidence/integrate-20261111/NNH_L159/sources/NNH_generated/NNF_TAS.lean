import NNF_Folds
import NNF_Reify
set_option autoImplicit false
namespace NNF_TAS
open RSL
open RSL.TX2_241 (V2Lib)
open RSL.TX1_345 (S1Lib)
/-- Install the emitted dispatcher interpretation into the shared Impl.
All non-dispatcher fields, especially the two actual wrapper functions, are
unchanged. No arbitrary Impl process/entry is assumed equal to a reference. -/
def install {L : PoolLib} {V0 : V2Lib} {VL : VLib} (I : TAS.Impl L V0 VL) :
    TAS.Impl L V0 VL :=
  { I with
    process := NNF_Dispatch.process I.f344 I.f240
    entry := NNF_Dispatch.entry (NNF_Dispatch.process I.f344 I.f240) }

/-- Exactly TAS_Interfaces.NMW_Roots.r221, parametric in every V2Lib. -/
theorem r221 (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : TAS.Impl L V0 VL) :
    ∀ V : V2Lib, TX1_344.RowSpec_344 VL P C (install I).f344 →
      TX2_240.RowSpec_240 L D V (install I).f240 →
      TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) (install I).process :=
  fun V h1 h2 => NNF_Folds.process_tx2 L D V VL P C I.f344 I.f240 h1 h2

/-- Exactly TAS_Interfaces.NMW_Roots.r213; same arbitrary library V. -/
theorem r213 (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : TAS.Impl L V0 VL) :
    ∀ V : V2Lib,
      TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) (install I).process →
      TX2_213.RowSpec_213 L D V (TX1_344.asStage1 VL P C) (install I).entry :=
  fun V h => NNF_Folds.entry_tx2 L D V VL P C (install I).process h

/-- Kernel-checked inhabitant of the actual TAS interface (no duplicate kit). -/
theorem roots (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : TAS.Impl L V0 VL) :
    TAS.NMW_Roots (L := L) (D := D) (V0 := V0) (VL := VL) (P := P) (C := C)
      (I := install I) :=
  ⟨r221 L D V0 VL P C I, r213 L D V0 VL P C I⟩

/-- G1b regression: the SAME package inhabits the weak-library case. -/
theorem weak_process (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : TAS.Impl L V0 VL)
    (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
    (h1 : TX1_344.RowSpec_344 VL P C I.f344)
    (h2 : TX2_240.RowSpec_240 L D (TCK.weaken V0 w) I.f240) :
    TX2_221.RowSpec_221 L D (TCK.weaken V0 w)
      (TX1_344.asStage1 VL P C) (install I).process :=
  (roots L D V0 VL P C I).r221 (TCK.weaken V0 w) h1 h2
/-- Unconditional weak entry law from the same parametric folds. No native
stage2=model equality or Root0 premise is introduced off the canonical domain. -/
theorem weak_entry (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : TAS.Impl L V0 VL)
    (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
    (h1 : TX1_344.RowSpec_344 VL P C I.f344)
    (h2 : TX2_240.RowSpec_240 L D (TCK.weaken V0 w) I.f240) :
    ∀ a s env, TX2_213.Ref L D (TCK.weaken V0 w) (TX1_344.asStage1 VL P C)
      a s env ((install I).entry a s env) := by
  apply TCK.entry_weak_unconditional L D V0 w VL P C (install I).entry
  exact (roots L D V0 VL P C I).r213 (TCK.weaken V0 w)
    (weak_process L D V0 VL P C I w h1 h2)
#print axioms weak_entry
#print axioms r221
#print axioms r213
#print axioms roots
#print axioms weak_process
end NNF_TAS
