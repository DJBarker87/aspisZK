import R1Z.ProverCommitReservationRom37
/-! Byte grammar criteria for the source audit. These universal lemmas do
not assert that a source inventory is a verified complete call graph. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReservationFrames37
open R0Z.FsStatement ProverCommitReservationRom37

theorem reservation_injective : Function.Injective reservationInput := by
  intro nonce other eq
  have suffix : List.ofFn nonce = List.ofFn other := List.append_cancel_left eq
  simpa only [List.ofFn_inj] using suffix

theorem reservation_control (nonce : OracleAnswer) :
    ((reservationInput nonce).drop 32).head? = some (116 : UInt8) := by rfl

theorem first_byte_separated (nonce : OracleAnswer) (tag : UInt8)
    (different : tag ≠ 97) (suffix : List UInt8) :
    reservationInput nonce ≠ tag::suffix := by
  intro eq
  have h := congrArg List.head? eq
  change some (97 : UInt8) = some tag at h
  exact different (Option.some.inj h).symm

theorem state_control_separated (nonce : OracleAnswer) (state : List UInt8)
    (length : state.length = 32) (tag : UInt8) (different : tag ≠ 116)
    (suffix : List UInt8) :
    reservationInput nonce ≠ state ++ tag::suffix := by
  intro eq
  have empty : state.drop 32 = [] := by rw [← length,List.drop_length]
  have h := congrArg (fun xs : List UInt8 => (xs.drop 32).head?) eq
  rw [reservation_control] at h
  simp only [List.drop_append,empty,length,Nat.sub_self,List.drop_zero,
    List.nil_append,List.head?_cons] at h
  exact different (Option.some.inj h).symm

#print axioms reservation_injective
#print axioms reservation_control
#print axioms first_byte_separated
#print axioms state_control_separated
end R1Z.ProverCommitReservationFrames37
