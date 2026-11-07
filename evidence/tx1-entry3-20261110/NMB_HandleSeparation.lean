import NMB_AcceptedExtents
set_option autoImplicit false
noncomputable section
namespace NMB_HandleSeparation
open Aeneas Aeneas.Std Result AspisR1
/-- Different decoder-admitted extents exclude aliasing, without ever
identifying account-occurrence flags by their cell. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (saved : alloc.vec.Vec U8)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 (x.handles 0).1≠(x.handles 1).1 ∧
 (x.handles 0).1≠(x.handles 2).1 ∧
 (x.handles 1).1≠(x.handles 2).1 := by
 obtain ⟨proof,pub,cp⟩ := NMB_AcceptedExtents.source x ops p d saved accepted
 refine ⟨?_,?_,?_⟩
 · intro eq; rw [eq] at proof; omega
 · intro eq; rw [eq] at proof; omega
 · intro eq; rw [eq] at pub; omega
#print source
#print axioms source
end NMB_HandleSeparation
