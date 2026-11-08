import PV_LIB_A_RangeInvariant12
import PV_THR2_IntrinsicFrameEnter
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CallFrame13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_StoreActionTable

/-- Argument binding writes only the freshly selected callee activation. It
frames arbitrary older caller cells, without equating activation counters. -/
theorem arguments_frame (s : Store Data) (child first : Nat) (args : List Data)
    (p : Address) (older : p.activation < child) :
    (PV_STX2_Native.arguments child args first s).cells p = s.cells p := by
  induction args generalizing s first with
  | nil => rfl
  | cons v vs ih =>
    rw [PV_STX2_Native.arguments,ih]
    apply write_other
    intro eq
    have bad := congrArg Address.activation eq
    exact (Nat.ne_of_lt older) bad

theorem issued_frame (s : Store Data) (args : List Data) (p : Address)
    (older : p.activation < s.nextActivation) :
    (PV_THR2_StaticCall.issued s args).cells p = s.cells p :=
  arguments_frame {s with nextActivation := s.nextActivation+1} s.nextActivation 1 args p older

theorem entered_iterator (s : Store Data) (a start finish : Nat)
    (parents : List Frame) (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (fn : Data) (args : List Data) (dest : Nat) (body : PV_STX2_SliceSyntax.Program)
    (numbered : a < s.nextActivation)
    (iterator : PV_LIB_A_RangeInvariant12.Iterator s a start finish) :
    PV_LIB_A_RangeInvariant12.Iterator
      (PV_THR2_IntrinsicFrameEnter.entered s a parents loops rest fn args dest body).store a start finish := by
  unfold PV_LIB_A_RangeInvariant12.Iterator
  rw [show (PV_THR2_IntrinsicFrameEnter.entered s a parents loops rest fn args dest body).store =
    PV_THR2_StaticCall.issued s args from rfl,issued_frame s args ⟨a,7,[]⟩ numbered]
  exact iterator

/-- Return administration writes the child return0 and the caller destination.
A disjoint caller iterator is preserved for every returned payload. This does
not certify the callee's internal/native writes or a successful return. -/
theorem returned_iterator (s : Store Data) (child a dest start finish : Nat) (v : Data)
    (different : a ≠ child) (notIterator : dest ≠ 7)
    (iterator : PV_LIB_A_RangeInvariant12.Iterator s a start finish) :
    PV_LIB_A_RangeInvariant12.Iterator
      (write (write s ⟨child,0,[]⟩ (some v)) ⟨a,dest,[]⟩ (some v)) a start finish := by
  unfold PV_LIB_A_RangeInvariant12.Iterator
  rw [write_other,write_other]
  · exact iterator
  · intro eq; exact different (congrArg Address.activation eq)
  · intro eq; exact notIterator (congrArg Address.localIndex eq).symm

#print axioms arguments_frame
#print axioms issued_frame
#print axioms entered_iterator
#print axioms returned_iterator
end PV_LIB_A_CallFrame13
