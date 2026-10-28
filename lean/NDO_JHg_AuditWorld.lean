import NDO_JHg_StoreOwner
import NDO_JHb_Owners
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_AuditWorld
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers
attribute [local irreducible] JHg_World.buffer JHb_World.buffer
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint JHb_Header.account

theorem key (a x y : Nat) : (JHg_World.e2.snapshot a x y).key =
    (JHb_World.e2.snapshot a x y).key := by
  unfold JHg_World.e2 JHb_World.e2
  rfl
#print axioms key
theorem owner (a x y : Nat) : (JHg_World.e2.snapshot a x y).owner =
    (JHb_World.e2.snapshot a x y).owner := by
  have left : (JHg_World.e2.snapshot a x y).owner=JHg_World.owner (CPH_FixtureData.readerCell a) := by
    change (Hist_RuntimeEntry.commit (CPG_Projection.cached JHg_World.initial).cells
      2 JFv_World.saved (CPH_FixtureData.readerCell a)).owner=JHg_World.owner _
    rw [JHg_StoreOwner.all]
    rfl
  have right : (JHb_World.e2.snapshot a x y).owner=JHb_World.owner (CPH_FixtureData.readerCell a) := by
    change (Hist_RuntimeEntry.commit (CPG_Projection.cached JHb_World.initial).cells
      2 JFv_World.saved (CPH_FixtureData.readerCell a)).owner=JHb_World.owner _
    rw [JHg_StoreOwner.all]
    rfl
  exact left.trans right.symm
#print axioms owner
theorem signer (a x y : Nat) : (JHg_World.e2.snapshot a x y).is_signer=false := by
  unfold JHg_World.e2
  rfl
#print axioms signer
theorem writable (a x y : Nat) : (JHg_World.e2.snapshot a x y).is_writable=false := by
  unfold JHg_World.e2
  rfl
#print axioms writable
theorem executable (a x y : Nat) : (JHg_World.e2.snapshot a x y).executable=false := by
  unfold JHg_World.e2
  rfl
#print axioms executable
theorem handles : JHg_World.e2.handles=JHb_World.e2.handles := by
  unfold JHg_World.e2 JHb_World.e2
  rfl
#print axioms handles
theorem base : JHg_World.e2.base=JHb_World.e2.base := by
  unfold JHg_World.e2 JHb_World.e2
  rfl
#print axioms base
theorem provenance : JHg_World.e2.provenance=JHb_World.e2.provenance := by
  unfold JHg_World.e2 JHb_World.e2
  rfl
#print axioms provenance
theorem proof : JHg_World.e2.buffers (JHg_World.e2.handles 0).1=JHb_Header.account := by
  unfold JHg_World.e2
  change JHg_World.buffer 0=JHb_Header.account
  unfold JHg_World.buffer
  rfl
#print axioms proof
theorem publicInput : JHg_World.e1.buffers (JHg_World.e1.handles 1).1=JFx_NativeBytes.publicInput := by
  change JHg_World.buffer 1=JFx_NativeBytes.publicInput
  unfold JHg_World.buffer
  rfl
#print axioms publicInput
theorem checkpoint : JHg_World.e2.buffers (JHg_World.e2.handles 6).1=JFx_NativeBytes.checkpoint := by
  unfold JHg_World.e2
  rfl
#print axioms checkpoint
theorem saved : JFv_World.saved.val=JFx_NativeBytes.checkpoint.val := rfl
#print axioms saved
end AspisR1.JHg_AuditWorld
end
