import NDE_Reference10.Funs
import NDE_VariantBridge
import RPv_FIx_ReconstructStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_LinearSteps
abbrev Q := NDE_Reference10.Q

def toOld (q : Q) : NDE_Reference3.Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
abbrev toNative (q : Q) := NDE_VariantBridge.toNative (toOld q)

theorem map_comp {α β γ : Type} (f : β → γ) (g : α → β) (r : Result α) :
    NDE_LiftBridge.mapResult f (NDE_LiftBridge.mapResult g r) =
    NDE_LiftBridge.mapResult (fun x => f (g x)) r := by cases r <;> rfl

theorem bind_map {α β γ : Type} (f : α → β) (r : Result α) (k : β → Result γ) :
    (do let x ← NDE_LiftBridge.mapResult f r; k x) =
    (do let x ← r; k (f x)) := by cases r <;> rfl

theorem add_port (a b : Q) :
    NDE_LiftBridge.mapResult toOld (NDE_Reference10.add_ref a b) =
    NDE_Reference3.add_ref (toOld a) (toOld b) := by
  simp only [NDE_Reference10.add_ref,NDE_Reference3.add_ref,NDE_RawBridge.map_bind]
  rfl

theorem add_native (a b : Q) :
    NDE_LiftBridge.mapResult toNative (NDE_Reference10.add_ref a b) =
    FIq_Native.field.QM31.add (toNative a) (toNative b) := by
  have h := NDE_VariantBridge.add_reference (toOld a) (toOld b)
  rw [← add_port] at h
  simpa only [map_comp,toNative] using h

theorem sum_step (a b : Q) :
    NDE_LiftBridge.mapResult toNative (NDE_Reference10.sum_step_ref a b) =
    FIq_Native.field.QM31.add (toNative a) (toNative b) := by
  exact add_native a b

theorem reconstruct_step (a bit : Q) :
    NDE_LiftBridge.mapResult toNative (NDE_Reference10.reconstruct_step_ref a bit) =
    (do let doubled ← FIq_Native.field.QM31.add (toNative a) (toNative a)
        FIq_Native.field.QM31.add doubled (toNative bit)) := by
  calc
    _ = (do let doubled ← NDE_Reference10.add_ref a a
            FIq_Native.field.QM31.add (toNative doubled) (toNative bit)) := by
          simp only [NDE_Reference10.reconstruct_step_ref,NDE_RawBridge.map_bind,add_native]
    _ = (do let doubled ← NDE_LiftBridge.mapResult toNative (NDE_Reference10.add_ref a a)
            FIq_Native.field.QM31.add doubled (toNative bit)) := (bind_map toNative (NDE_Reference10.add_ref a a) (fun d => FIq_Native.field.QM31.add d (toNative bit))).symm
    _ = _ := by rw [add_native]

#print axioms map_comp
#print axioms bind_map
#print axioms add_port
#print axioms add_native
#print axioms sum_step
#print axioms reconstruct_step
end NDE_LinearSteps
