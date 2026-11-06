import NLF_ExclusiveBracket
set_option autoImplicit false
namespace NLF_CopyStep
open NLF_RefCell NLF_SdkModel
inductive Outcome where
  | returned (state : State) (reply : Except ProgramError Unit)
  | abort (state : State)

def run (s : State) (a t : Nat) (src : List UInt8) : Outcome :=
  match try_borrow_mut_data s a t with
  | (s', .error e) => .returned s' (.error e)
  | (s', .ok g) =>
    let p := deref s' g
    if src.length=p.bytes.length then
      let v := {p with bytes:=NLF_CopyValue.copy src p.bytes 0 src.length}
      match release (NLF_ViewLaws.write s' g v) g with
      | .ok s'' => .returned s'' (.ok ())
      | .error _ => .abort s'
    else .abort s'

theorem conflict (s : State) (a t : Nat) (src : List UInt8)
    (bad : ¬ ((s.cells (s.accounts a).data).writer=none ∧ (s.cells (s.accounts a).data).readers=[])) :
    run s a t src = .returned s (.error .accountBorrowFailed) := by
  simp [run,try_borrow_mut_data,wrap,exclusive,bad]

theorem wrong_length (s : State) (a t : Nat) (src : List UInt8)
    (free : (s.cells (s.accounts a).data).writer=none)
    (empty : (s.cells (s.accounts a).data).readers=[])
    (bad : src.length≠(s.cells (s.accounts a).data).payload.bytes.length) :
    run s a t src = .abort (put s (s.accounts a).data {s.cells (s.accounts a).data with writer:=some t}) := by
  unfold run try_borrow_mut_data
  rw [exclusive_result s _ t free empty]
  simp only [exclusive_deref]
  simp [bad]

theorem success (s : State) (a t : Nat) (src : List UInt8)
    (free : (s.cells (s.accounts a).data).writer=none)
    (empty : (s.cells (s.accounts a).data).readers=[])
    (same : src.length=(s.cells (s.accounts a).data).payload.bytes.length) :
    run s a t src = .returned (put s (s.accounts a).data
      {s.cells (s.accounts a).data with payload:={(s.cells (s.accounts a).data).payload with bytes:=src}}) (.ok ()) := by
  unfold run try_borrow_mut_data
  rw [exclusive_result s _ t free empty]
  simp only [exclusive_deref]
  rw [if_pos same,NLF_StateLaws.write_release s _ t _ free]
  rw [same,NLF_CopyValue.copy_whole src _ same]

#print axioms conflict
#print axioms wrong_length
#print axioms success
end NLF_CopyStep
