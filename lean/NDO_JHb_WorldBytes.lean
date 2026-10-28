import NDO_JHb_World
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_WorldBytes
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open JHb_World CPG_Projection CPP_BankState Hist_RuntimeEntry
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint JHb_Header.account e1 e2

theorem inputs :
    e1.buffers (e1.handles 0).1=JHb_Header.account ∧
    e2.buffers (e2.handles 0).1=JHb_Header.account ∧
    e1.buffers (e1.handles 1).1=JFx_NativeBytes.publicInput ∧
    e2.buffers (e2.handles 6).1=JFx_NativeBytes.checkpoint := by
  unfold e1 e2
  exact ⟨rfl,rfl,rfl,rfl⟩
#print axioms inputs
end AspisR1.JHb_WorldBytes
end
