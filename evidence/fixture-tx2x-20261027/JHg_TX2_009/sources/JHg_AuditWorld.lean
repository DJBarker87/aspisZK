import JHg_World
import JHb_Owners
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_AuditWorld
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint JHb_Header.account

theorem key (a x y : Nat) : (JHg_World.e2.snapshot a x y).key =
    (JHb_World.e2.snapshot a x y).key := rfl
#print axioms key
theorem owner (a x y : Nat) : (JHg_World.e2.snapshot a x y).owner =
    (JHb_World.e2.snapshot a x y).owner := rfl
#print axioms owner
theorem signer (a x y : Nat) : (JHg_World.e2.snapshot a x y).is_signer=false := rfl
#print axioms signer
theorem writable (a x y : Nat) : (JHg_World.e2.snapshot a x y).is_writable=false := rfl
#print axioms writable
theorem executable (a x y : Nat) : (JHg_World.e2.snapshot a x y).executable=false := rfl
#print axioms executable
theorem records : JHg_World.e2.records=JHb_World.e2.records := rfl
#print axioms records
theorem handles : JHg_World.e2.handles=JHb_World.e2.handles := rfl
#print axioms handles
theorem base : JHg_World.e2.base=JHb_World.e2.base := rfl
#print axioms base
theorem provenance : JHg_World.e2.provenance=JHb_World.e2.provenance := rfl
#print axioms provenance
theorem proof : JHg_World.e2.buffers (JHg_World.e2.handles 0).1=JHb_Header.account := rfl
#print axioms proof
theorem publicInput : JHg_World.e1.buffers (JHg_World.e1.handles 1).1=JFx_NativeBytes.publicInput := rfl
#print axioms publicInput
theorem checkpoint : JHg_World.e2.buffers (JHg_World.e2.handles 6).1=JFx_NativeBytes.checkpoint := rfl
#print axioms checkpoint
theorem saved : JFv_World.saved.val=JFx_NativeBytes.checkpoint.val := rfl
#print axioms saved
end AspisR1.JHg_AuditWorld
end
