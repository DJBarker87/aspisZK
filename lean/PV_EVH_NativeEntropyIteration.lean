import PV_EVH_StackEntropyFill
import PV_EVH_NativeEntropyBorrow
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyIteration
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)

def initial : Array U8 64#usize := Array.repeat 64#usize 0#u8
def buffer : Slice U8 := (Array.to_slice_mut initial).1
def restore : Slice U8 → zeroize.Zeroizing (Array U8 64#usize) :=
  (Array.to_slice_mut initial).2

/-- Source iteration prelude, with stack lifetime admission and the native
fill/error cleanup installed. Success remains an explicit continuation, so this
definition is not yet a complete native interpreter for the entropy loop. -/
def run [ExternalTypes] [ExternalFuns]
    (mask : Array U8 32#usize) (limit retry : Usize) (slot : Slot)
    (driver : Slice U8 → State → PV_EVH_StackEntropyFill.Delivery)
    (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer) :
    Q Answer := do
  if retry < limit then
    let bytes ← PV_EVH_StackCleanup.lift (zeroize.Zeroizing.new
      (Array.Insts.ZeroizeZeroize 64#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) initial)
    let _ ← fun w =>
      (⟨.returned (.ok ()),PV_EVH_StackAdmission.enter slot
        (PV_EVH_StackEntropyFill.encode bytes) w,[]⟩ : PV_EVH_StackCleanup.Run Unit)
    let (s,back) ← PV_EVH_StackCleanup.lift
      (zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut
        (Array.Insts.CoreConvertAsMutSlice U8 64#usize)
        (Array.Insts.ZeroizeZeroize 64#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) bytes)
    PV_EVH_NativeEntropyError.afterFill slot.key
      (PV_EVH_StackEntropyFill.fill slot driver s) (success back)
  else
    pure (done (.Err .RepeatedZeroBlock))

/-- Only a reached source call is fixed. No uniform dictionary-success domain
or successful prover run is assumed. -/
theorem source_error (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize)
      (e : getrandom.error.Error) (s : Slice U8), retry < limit →
      getrandom.fill buffer = .ok (.Err e,s) →
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = .ok (PV_EVH_NativeEntropyError.returnedError e) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry e s hr hf
  simp only [aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body,
    hr,if_true]
  rw [PV_EVH_NativeZeroWrappers.constructor_native base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_EVH_NativeEntropyBorrow.array_borrow base heap box ops]
  simp only [bind_tc_ok]
  change (do let (r,s1) ← getrandom.fill buffer
             PV_EVH_Entropy.afterDraw mask retry restore r s1) = _
  rw [hf]
  rfl

theorem run_step (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (slot : Slot)
      (driver : Slice U8 → State → PV_EVH_StackEntropyFill.Delivery)
      (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer)
      (w : State), retry < limit →
      run mask limit retry slot driver success w =
        PV_EVH_NativeEntropyError.afterFill slot.key
          (PV_EVH_StackEntropyFill.fill slot driver buffer) (success restore)
          (PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry slot driver success w hr
  simp only [run,hr,if_true]
  rw [PV_EVH_NativeZeroWrappers.constructor_native base heap box ops]
  simp only [Bind.bind,PV_EVH_StackCleanup.bind,PV_EVH_StackCleanup.lift]
  rw [PV_EVH_NativeEntropyBorrow.array_borrow base heap box ops]
  simp only [PV_EVH_StackCleanup.bind,PV_EVH_StackCleanup.lift,List.nil_append]
  rfl

#print axioms source_error
#print axioms run_step
end PV_EVH_NativeEntropyIteration
