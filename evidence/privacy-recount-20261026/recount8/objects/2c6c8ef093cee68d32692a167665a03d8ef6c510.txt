import R1Z.ProverCommitPrimitive47
import R1Z.ProverCommitValueRange47
/-! Exact arithmetic closure of canonical embedded QM31 values for the
explicitly overflow-checked extracted WideExact operations. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSubfieldOps47
open Aeneas Aeneas.Std Result
open AspisR1ProducerChecked47
open ProverCommitPrimitive47
open AspisR1.ExtractedCurrentQM31Exact
abbrev Canonical := CurrentCanonicalQM
abbrev E := field.wide_exact.WideExact

def zero : Old.Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def embedded (x : Old.Q) : E := ⟨fromQ x,fromQ zero⟩

theorem zero_canonical : Canonical zero := ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩

theorem zero_decode : decode zero = 0 := rfl

theorem qadd_zero (x : Old.Q) (hx : Canonical x) :
    field.QM31.add (fromQ x) (fromQ zero) = ok (fromQ x) := by
  obtain ⟨z,hz,hcanon,heq⟩ := current_qm_add_exact x zero hx zero_canonical
  have he : z=x := (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff z x hcanon hx).mp
    (by simpa only [zero_decode,add_zero] using heq)
  rw [addQ,hz,he]
  rfl

theorem qmul_zero (x : Old.Q) (hx : Canonical x) :
    field.QM31.mul (fromQ x) (fromQ zero) = ok (fromQ zero) := by
  obtain ⟨z,hz,hcanon,heq⟩ := current_qm_mul_exact x zero hx zero_canonical
  have he : z=zero := (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff z zero hcanon zero_canonical).mp
    (by simpa only [zero_decode,mul_zero] using heq)
  rw [mulQ,hz,he]
  rfl

theorem subC_self (x : Old.C)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM x) :
    field.CM31.sub (fromC x) (fromC x) = ok (fromC ⟨0#u32,0#u32⟩) := by
  obtain ⟨z,hz,hcanon,ha,hb⟩ := AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod x x hx hx
  have va : z.a.val=0 := by simpa only [Nat.add_sub_cancel_left,Nat.mod_self] using ha
  have vb : z.b.val=0 := by simpa only [Nat.add_sub_cancel_left,Nat.mod_self] using hb
  have ea : z.a=0#u32 := UScalar.val_eq_imp _ _ va
  have eb : z.b=0#u32 := UScalar.val_eq_imp _ _ vb
  have he : z=⟨0#u32,0#u32⟩ := by cases z; simp_all
  rw [subC,hz,he]
  rfl

theorem sub_self (x : Old.Q) (hx : Canonical x) :
    field.QM31.sub (fromQ x) (fromQ x) = ok (fromQ zero) := by
  unfold field.QM31.sub fromQ
  rw [subC_self x.c0 hx.1,subC_self x.c1 hx.2]
  rfl

theorem mul_u_zero : field.wide_exact.mul_u (fromQ zero) = ok (fromQ zero) := by
  simp only [field.wide_exact.mul_u,field.mul_by_r,field.M31.double,
    field.M31.add,field.M31.sub,field.P,fromQ,fromC,zero]
  rfl

/-- WideExact addition really preserves the raw canonical embedding and
has the retained exact-field value; no callee-success premise is supplied. -/
theorem embedded_add (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, field.wide_exact.WideExact.add (embedded x) (embedded y) = ok (embedded z) ∧
      Canonical z ∧ decode z = decode x + decode y := by
  obtain ⟨z,hz,hcanon,heq⟩ := current_qm_add_exact x y hx hy
  refine ⟨z,?_,hcanon,heq⟩
  have main : field.QM31.add (fromQ x) (fromQ y)=ok (fromQ z) := by rw [addQ,hz];rfl
  simp only [field.wide_exact.WideExact.add,embedded,main,qadd_zero zero zero_canonical,bind_tc_ok]

/-- Canonical embedded multiplication, including Karatsuba's cancelling high
coordinate. The native release/checked relation remains separate. -/
theorem embedded_mul (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, field.wide_exact.WideExact.mul (embedded x) (embedded y) = ok (embedded z) ∧
      Canonical z ∧ decode z = decode x * decode y := by
  obtain ⟨z,hz,hcanon,heq⟩ := current_qm_mul_exact x y hx hy
  have main : field.QM31.mul (fromQ x) (fromQ y)=ok (fromQ z) := by rw [mulQ,hz];rfl
  refine ⟨z,?_,hcanon,heq⟩
  simp only [field.wide_exact.WideExact.mul,embedded,main,qmul_zero zero zero_canonical,
    qadd_zero x hx,qadd_zero y hy,mul_u_zero,qadd_zero z hcanon,sub_self z hcanon,
    sub_self zero zero_canonical,bind_tc_ok]

#print axioms zero_canonical
#print axioms zero_decode
#print axioms qadd_zero
#print axioms qmul_zero
#print axioms subC_self
#print axioms sub_self
#print axioms mul_u_zero
#print axioms embedded_add
#print axioms embedded_mul
end R1Z.ProverCommitSubfieldOps47
