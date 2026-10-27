import R1Z.PV_L2_Record
import R1Z.CertCheckDot

/-! Exact operational one-iteration factorization of the extracted c3 dot
checker. No success is assumed for arithmetic or indexing; the increment
lemma is conditional only on that concrete step returning successfully. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6DotStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck
open R1Z.PV_L2_Record

/-- Exact checked operations of dot_loop, in their extracted order. -/
def step (a : Slice U32) (ao ast : Usize) (b : Slice U32)
    (bo bst : Usize) (acc : U64) (p : Usize) : Result (U64 × Usize) := do
  let i ← p * ast
  let i1 ← ao + i
  let i2 ← Slice.index_usize a i1
  let x ← lift (UScalar.cast .U64 i2)
  let i3 ← p * bst
  let i4 ← bo + i3
  let i5 ← Slice.index_usize b i4
  let y ← lift (UScalar.cast .U64 i5)
  let i6 ← x * y
  let i7 ← i6 % P
  let acc1 ← acc + i7
  let p1 ← p + 1#usize
  ok (acc1,p1)

def recorded (a : Slice U32) (ao ast : Usize) (b : Slice U32)
    (bo bst : Usize) (acc : U64) (p : Usize) : Recorded (U64 × Usize) := do
  let i ← operation (.mul p.val ast.val) (p * ast)
  let i1 ← operation (.add ao.val i.val) (ao + i)
  let i2 ← operation (.index 0 i1.val) (Slice.index_usize a i1)
  let x := UScalar.cast .U64 i2
  let i3 ← operation (.mul p.val bst.val) (p * bst)
  let i4 ← operation (.add bo.val i3.val) (bo + i3)
  let i5 ← operation (.index 1 i4.val) (Slice.index_usize b i4)
  let y := UScalar.cast .U64 i5
  let i6 ← operation (.mul x.val y.val) (x * y)
  let i7 ← operation (.rem i6.val P.val) (i6 % P)
  let acc1 ← operation (.add acc.val i7.val) (acc + i7)
  let p1 ← operation (.add p.val 1) (p + 1#usize)
  PV_L2_Record.pure (acc1,p1)

theorem recorded_erases (a : Slice U32) (ao ast : Usize) (b : Slice U32)
    (bo bst : Usize) (acc : U64) (p : Usize) :
    (recorded a ao ast b bo bst acc p).value = step a ao ast b bo bst acc p := by
  simp only [recorded,operation_bind_value,pure_value,step,lift,bind_tc_ok]

theorem unroll (a : Slice U32) (ao ast : Usize) (b : Slice U32)
    (bo bst n : Usize) (acc : U64) (p : Usize) :
    dot_loop a ao ast b bo bst n acc p =
      if p < n then (do
        let (acc1,p1) ← step a ao ast b bo bst acc p
        dot_loop a ao ast b bo bst n acc1 p1) else ok acc := by
  rw [dot_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (a : Slice U32) (ao ast : Usize) (b : Slice U32)
    (bo bst : Usize) (acc : U64) (p : Usize) (after : U64 × Usize)
    (success : step a ao ast b bo bst acc p = ok after) : after.2.val = p.val+1 := by
  unfold step at success
  obtain ⟨i,hi,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨i2,hi2,success⟩ := bind_eq_ok success
  obtain ⟨x,hx,success⟩ := bind_eq_ok success
  obtain ⟨i3,hi3,success⟩ := bind_eq_ok success
  obtain ⟨i4,hi4,success⟩ := bind_eq_ok success
  obtain ⟨i5,hi5,success⟩ := bind_eq_ok success
  obtain ⟨y,hy,success⟩ := bind_eq_ok success
  obtain ⟨i6,hi6,success⟩ := bind_eq_ok success
  obtain ⟨i7,hi7,success⟩ := bind_eq_ok success
  obtain ⟨acc1,hacc1,success⟩ := bind_eq_ok success
  obtain ⟨p1,hp1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [← he]
  have hv := add_ok hp1
  simpa only [show (1#usize).val=1 from rfl] using hv

#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6DotStep
