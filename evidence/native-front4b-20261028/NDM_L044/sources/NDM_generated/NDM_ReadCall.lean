import NDM_EntryCarrier
import NCV_Install
set_option autoImplicit false
namespace NDM_ReadCall
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.S2W_D189Entry

/-- Exact data-then-free-slot suffix used by authentication/validation. The
 enclosing prefix and physical receiver association are separate obligations. -/
def source {A : Type} (ops : Ops)
 (callee : Slice U8 → Result (core.result.Result A solana_program_error.ProgramError))
 (a : r1_pool_adapter.owned.OwnedAccount) := do
 let input ← r1_pool_adapter.owned.OwnedAccount.data ops a
 match input with | .Ok bytes=>callee bytes | .Err e=>ok (.Err e)

theorem admitted {A : Type} (ops : Ops)
 (callee : Slice U8 → Result (core.result.Result A solana_program_error.ProgramError))
 (e : Entry) (a l1 l2 : Nat) (h : NDM_EntryCarrier.admitted e a l1 l2) :
 source ops callee (e.snapshot a l1 l2)=callee (alloc.vec.Vec.deref (e.buffers (e.handles a).1)) := by
 unfold source
 rw [NDM_EntryCarrier.data_success ops e a l1 l2 h]
 rfl

theorem rejected {A : Type} (ops : Ops)
 (callee : Slice U8 → Result (core.result.Result A solana_program_error.ProgramError))
 (e : Entry) (a l1 l2 : Nat) (h : ¬ NDM_EntryCarrier.admitted e a l1 l2)
 (clone : ops.op35 .InvalidAccountData=ok .InvalidAccountData) :
 source ops callee (e.snapshot a l1 l2)=ok (.Err .InvalidAccountData) := by
 unfold source
 rw [NDM_EntryCarrier.data_error ops e a l1 l2 h clone]
 rfl

/-- Reuse the existing decoder representation; no decoder-body proof is repeated. -/
theorem lane (base : Ops) (e : Entry) (a l1 l2 : Nat)
 (h : NDM_EntryCarrier.admitted e a l1 l2) :
 source (NCV_Install.install base) (NCV_Install.install base).op50 (e.snapshot a l1 l2)=
 NCV_Install.op50 (alloc.vec.Vec.deref (e.buffers (e.handles a).1)) :=
 admitted _ _ e a l1 l2 h

theorem scan (base : Ops) (e : Entry) (a l1 l2 : Nat)
 (h : NDM_EntryCarrier.admitted e a l1 l2) :
 source base base.op51 (e.snapshot a l1 l2)=
 base.op51 (alloc.vec.Vec.deref (e.buffers (e.handles a).1)) :=
 admitted _ _ e a l1 l2 h

#print axioms admitted
#print axioms rejected
#print axioms lane
#print axioms scan
end NDM_ReadCall
