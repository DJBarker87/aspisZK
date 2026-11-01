import PV_EVH_NonzeroFlow
import PV_EVH_EntropyStep
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonzeroInstall
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Remaining entropy leaves only; no whole nonzero answer is accepted. -/
structure Callees where
  op128_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), P ((zeroize.Zeroizing Z))
  op125_OPEN : ∀ {T : Type} {Z : Type} (coreconvertAsMutInst : core.convert.AsMut Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P ((T × (T → zeroize.Zeroizing Z)))
  op126_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P ((Z × (Z → zeroize.Zeroizing Z)))
  op127_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P (Z)
  arrayIndex_OPEN : ∀ {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output) (a : Array T N) (i : I), P (Output)
  sliceCopy_OPEN : ∀ {T : Type} (inst : core.marker.Copy T) (dst src : Slice T), P (Slice T)

structure Compatible (c : Callees) : Prop where
  op128_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), FinishedView (c.op128_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.new ZeroizeInst arg0)
  op125_fixed : ∀ {T : Type} {Z : Type} (coreconvertAsMutInst : core.convert.AsMut Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op125_OPEN coreconvertAsMutInst ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut coreconvertAsMutInst ZeroizeInst arg0)
  op126_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op126_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut ZeroizeInst arg0)
  op127_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op127_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref ZeroizeInst arg0)
  arrayIndex_fixed : ∀ {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output) (a : Array T N) (i : I), FinishedView (c.arrayIndex_OPEN inst a i) (core.array.Array.index inst a i)
  sliceCopy_fixed : ∀ {T : Type} (inst : core.marker.Copy T) (dst src : Slice T), FinishedView (c.sliceCopy_OPEN inst dst src) (core.slice.Slice.copy_from_slice inst dst src)

def install (fuel : Nat) (c : Callees) : PV_EVH_EntropyStep.Callees where
  op128_OPEN := c.op128_OPEN
  op125_OPEN := c.op125_OPEN
  op126_OPEN := c.op126_OPEN
  op127_OPEN := c.op127_OPEN
  arrayIndex_OPEN := c.arrayIndex_OPEN
  sliceCopy_OPEN := c.sliceCopy_OPEN
  entropy_nonzero32_OPEN := PV_EVH_NonzeroFlow.run fuel

theorem install_fixed (fuel : Nat) (c : Callees) (hc : Compatible c) :
    PV_EVH_EntropyStep.Compatible (install fuel c) where
  op128_fixed := hc.op128_fixed
  op125_fixed := hc.op125_fixed
  op126_fixed := hc.op126_fixed
  op127_fixed := hc.op127_fixed
  arrayIndex_fixed := hc.arrayIndex_fixed
  sliceCopy_fixed := hc.sliceCopy_fixed
  entropy_nonzero32_fixed := PV_EVH_NonzeroFlow.run_fixed fuel
#print axioms install_fixed
end PV_EVH_NonzeroInstall
