import R1Z.PV_V263_VectorDrain
/-! Scalar and store laws for the SUFFICIENT-RESERVATION specialization of
Rust 1.94.1 Vec::append/append_elements/RawVecInner::reserve. The structural
source argument is recorded separately; this module is not an extraction. -/
set_option autoImplicit false
namespace R1Z.PV_V263_AppendBinding
open Aeneas Aeneas.Std PV_V263_VectorDrain

/-- Native needs_to_grow uses wrapping_sub; the no-wrap specialization is
justified below before its guard is simplified. -/
def wrappedRemaining (capacity length : Nat) : Nat :=
  (capacity + (Usize.max+1) - length) % (Usize.max+1)

theorem no_sub_wrap {A : Type} (out : Buffer A) :
    wrappedRemaining out.capacity out.values.length = out.capacity-out.values.length := by
  unfold wrappedRemaining
  have hf := out.fits
  have hb := out.bounded
  have rearrange : out.capacity+(Usize.max+1)-out.values.length =
      (out.capacity-out.values.length)+(Usize.max+1) := by omega
  rw [rearrange,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  apply Nat.mod_eq_of_lt
  omega

/-- Thus reserve cannot enter grow_amortized or handle_error on this branch.
This does not assert that arbitrary Vec push/append calls are infallible. -/
theorem reserve_no_growth {A : Type} (out source : Buffer A)
    (room : out.values.length+source.values.length ≤ out.capacity) :
    ¬ source.values.length > wrappedRemaining out.capacity out.values.length := by
  rw [no_sub_wrap]
  have hf := out.fits
  omega

theorem length_add_no_wrap {A : Type} (out source : Buffer A)
    (room : out.values.length+source.values.length ≤ out.capacity) :
    out.values.length+source.values.length ≤ Usize.max := room.trans out.bounded

/-- Native copy_nonoverlapping extends the initialized prefix; self.len+=count
publishes precisely that prefix; other.set_len(0) transfers all donor values.
The donor reservation survives until its destructor, including ZST buffers. -/
theorem stores {A : Type} (out source : Buffer A)
    (room : out.values.length+source.values.length ≤ out.capacity) :
    let after := drain out source room
    after.1.values.val = out.values.val ++ source.values.val ∧
    after.1.values.length = out.values.length+source.values.length ∧
    after.2.values.length = 0 ∧
    after.1.capacity = out.capacity ∧ after.2.capacity = source.capacity := by
  exact ⟨rfl,drain_length out source room,rfl,rfl,rfl⟩

/-- Public range boundaries supply exactly the room needed for the next family
when the previous families have been drained in source order. -/
theorem family_room (n k : Nat) (hk : k < 16) :
    PV_RunJoin_WorkRange35.start n k+PV_RunJoin_WorkRange35.width n k ≤ n :=
  PV_RunJoin_WorkRange35.bounded n k hk

#print axioms wrappedRemaining
#print axioms no_sub_wrap
#print axioms reserve_no_growth
#print axioms length_add_no_wrap
#print axioms stores
#print axioms family_room
end R1Z.PV_V263_AppendBinding
