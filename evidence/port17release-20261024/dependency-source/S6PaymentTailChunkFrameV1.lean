import S6PaymentCommonChunkFrameV1
set_option autoImplicit false
namespace AspisS6SliceFrame

theorem payment_transfer_tail {T : Type} (zero : T) (head recipient change : List T)
    (hh : head.length=148) (hr : recipient.length=32) (hc : change.length=32) :
    ((head++List.replicate 68 zero).setSlice! 152 recipient).setSlice! 184 change =
      head++List.replicate 4 zero++recipient++change := by
  have skip : head++List.replicate 68 zero =
      (head++List.replicate 4 zero)++List.replicate 64 zero := by
    rw [show (68 : Nat)=4+64 from rfl,List.replicate_add,List.append_assoc]
  rw [skip]
  have h1 := setSlice_append_chunk (head++List.replicate 4 zero) recipient 64 zero
    (by rw [hr]; decide)
  simp only [List.length_append,List.length_replicate,hh,hr,Nat.reduceAdd,Nat.reduceSub] at h1
  rw [h1]
  have h2 := setSlice_append_chunk ((head++List.replicate 4 zero)++recipient) change 32 zero
    (by rw [hc])
  simp only [List.length_append,List.length_replicate,hh,hr,hc,Nat.reduceAdd,Nat.reduceSub] at h2
  rw [h2]
  simp

theorem payment_withdrawal_tail {T : Type} (zero : T) (head amount destination change : List T)
    (hh : head.length=148) (ha : amount.length=4)
    (hd : destination.length=32) (hc : change.length=32) :
    (((head++List.replicate 68 zero).setSlice! 148 amount).setSlice! 152 destination).setSlice! 184 change =
      head++amount++destination++change := by
  have h0 := setSlice_append_chunk head amount 68 zero (by rw [ha]; decide)
  simp only [hh,ha,Nat.reduceSub] at h0
  rw [h0]
  have h1 := setSlice_append_chunk (head++amount) destination 64 zero (by rw [hd]; decide)
  simp only [List.length_append,hh,ha,hd,Nat.reduceAdd,Nat.reduceSub] at h1
  rw [h1]
  have h2 := setSlice_append_chunk ((head++amount)++destination) change 32 zero (by rw [hc])
  simp only [List.length_append,hh,ha,hd,hc,Nat.reduceAdd,Nat.reduceSub] at h2
  rw [h2]
  simp

#print axioms payment_transfer_tail
#print axioms payment_withdrawal_tail
end AspisS6SliceFrame
