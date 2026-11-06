import NLK_ProgramBorrowScope
set_option autoImplicit false
set_option pp.proofs false
namespace NLK_ReturningBorrow
open Aeneas Aeneas.Std Result NLF_RefCell NLF_SdkModel NLF_ParentModel
/-- Total RETURNED child, including its Err arm. No successful-acquisition or
successful-Drop premise. This is SDK scope support, not a native row root. -/
theorem complete {A : Type} (p : Parent) (a : Nat)
 (child : Payload → core.result.Result A AdapterRw.solana_program_error.ProgramError) :
 NLK_ProgramBorrowScope.run p a (fun b => ok (child b)) =
 let r := NLF_SnapshotEvents.step p a
 ⟨r.1,ok (match r.2 with | .ok b => child b | .error _ => .Err .AccountBorrowFailed)⟩ := by
 by_cases allowed : (p.state.cells (p.state.accounts a).data).writer=none ∧
   (p.state.cells (p.state.accounts a).data).readers.length<9223372036854775807 ∧
   p.next∉(p.state.cells (p.state.accounts a).data).readers
 · have acq := NLF_SdkModel.shared_result p.state (p.state.accounts a).data p.next
     allowed.1 allowed.2.2 allowed.2.1
   simp only [NLK_ProgramBorrowScope.run,NLK_ProgramBorrowScope.project,
     NLK_ProgramBorrowScope.liftChild,NLK_BorrowScope.run,
     acquire,NLF_SnapshotEvents.step,NLF_Bracket.snapshot,try_borrow_data]
   -- Keep the SDK wrapper opaque until its single acquisition law is applied.
   simp only [acq]
   simp [NLF_ParentModel.deref,live,put,NLF_SdkModel.deref,
     NLK_ProgramBorrowScope.liftChild,NLF_ParentModel.release,NLF_SdkModel.release,
     dropShared,NLF_SnapshotEvents.events,try_borrow_data,wrap,shared,
     allowed.1,allowed.2.1,allowed.2.2,List.append_assoc]
 · simp [NLK_ProgramBorrowScope.run,NLK_ProgramBorrowScope.project,
     NLK_ProgramBorrowScope.liftChild,NLK_BorrowScope.run,
     acquire,wrap,shared,allowed,NLF_SnapshotEvents.step,
     NLF_Bracket.snapshot,try_borrow_data,NLF_SnapshotEvents.events]
#print complete
#print axioms complete
end NLK_ReturningBorrow
