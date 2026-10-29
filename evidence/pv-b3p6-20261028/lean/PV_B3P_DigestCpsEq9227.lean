import PV_B3P_DigestContinue8227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227
set_option autoImplicit false

theorem bind_equal9 {α β : Type} (r : Result α) (f g : α → Result β)
    (h : ∀ x, f x=g x) : (r >>= f)=(r >>= g) :=
  congrArg (fun continuation => r >>= continuation) (funext h)

def recipient_action9 {β : Type} (recipient : Option DigestM) (output : DigestQ)
    (opened : Array aspis_core.field.QM31 16#usize) (selectors : reference_copy_terminal.Selectors)
    (f : DigestQ → Result β) : Result β :=
  match (generalizing := false) recipient with
  | none => f output
  | some expected => do
    let base ← lift (Usize.wrapping_mul 29#usize 16#usize)
    let row ← lift (Usize.wrapping_add base 11#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row
    let next ← reference_terminal.add_digest_binding output selector opened 0#usize expected false
    f next

theorem recipient_equal9 {β : Type} (recipient : Option DigestM) (output : DigestQ)
    (opened : Array aspis_core.field.QM31 16#usize) (selectors : reference_copy_terminal.Selectors)
    (f g : DigestQ → Result β) (h : ∀ next, f next=g next) :
    recipient_action9 recipient output opened selectors f =
      recipient_action9 recipient output opened selectors g :=
  congrArg (recipient_action9 recipient output opened selectors) (funext h)

def frontier_action9 {β : Type} (output : DigestQ) (opened : Array aspis_core.field.QM31 16#usize)
    (selectors : reference_copy_terminal.Selectors) (frontier : FrontierM)
    (level block : Usize) (bit : U64) (f : DigestQ → Result β) : Result β :=
  if bit=0#u64 then do
    let row ← lift (Usize.wrapping_mul block 16#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row
    let expected ← reference_terminal.empty_root level
    let next ← reference_terminal.add_digest_binding output selector opened aspis_statement.poseidon2.RATE expected true
    f next
  else do
    let base ← lift (Usize.wrapping_mul block 16#usize)
    let row ← lift (Usize.wrapping_add base 12#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row
    let expected ← reference_terminal.digest227 frontier level
    let next ← reference_terminal.add_digest_binding output selector opened 0#usize expected false
    f next

theorem frontier_equal9 {β : Type} (output : DigestQ) (opened : Array aspis_core.field.QM31 16#usize)
    (selectors : reference_copy_terminal.Selectors) (frontier : FrontierM)
    (level block : Usize) (bit : U64) (f g : DigestQ → Result β)
    (h : ∀ next, f next=g next) :
    frontier_action9 output opened selectors frontier level block bit f =
      frontier_action9 output opened selectors frontier level block bit g :=
  congrArg (frontier_action9 output opened selectors frontier level block bit) (funext h)

#print axioms bind_equal9
#print axioms recipient_equal9
#print axioms frontier_equal9
end PV_B3P_Binding9227
