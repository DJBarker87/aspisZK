import NEM_KindInstance
set_option autoImplicit false
noncomputable section
namespace NEQ_NullifierDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult
abbrev Payment := Sum NBN_ValidatorSummary.Transfer NBN_ValidatorSummary.Withdrawal

def paymentNullifier (p : Payment) : Array U32 8#usize :=
  match p with | .inl t => t.nullifier | .inr w => w.nullifier

theorem statement_result_frame {State : Type} (s : Statement) (state : State) :
    ((parts s).2.2.2.2.1,state,([] : List Unit)) =
      ((match s with | .PrivateTransfer _ p => p.nullifier | .Withdrawal _ p => p.nullifier),
       state,[]) := by
  rw [NBN_U05.validator_nullifier]
  rfl

theorem payment_result_frame {State : Type} (c : NBD_TerminalProjection.Common)
    (p : Payment) (state : State) :
    ((parts (NEM_KindInstance.join c p)).2.2.2.2.1,state,([] : List Unit)) =
      (paymentNullifier p,state,[]) := by
  cases p <;> exact statement_result_frame _ state

theorem common_independent (c c' : NBD_TerminalProjection.Common) (p : Payment) :
    (parts (NEM_KindInstance.join c p)).2.2.2.2.1 =
      (parts (NEM_KindInstance.join c' p)).2.2.2.2.1 := by
  have left := congrArg (fun x => x.1) (payment_result_frame c p ())
  have right := congrArg (fun x => x.1) (payment_result_frame c' p ())
  exact left.trans right.symm

#print axioms statement_result_frame
#print axioms payment_result_frame
#print axioms common_independent
end NEQ_NullifierDomains
