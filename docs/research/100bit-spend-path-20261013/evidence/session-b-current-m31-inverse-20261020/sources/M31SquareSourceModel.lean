import M31SquareRangeFacts
import R17CurrentM31Semantics

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1M31Inverse.SquareProof
open R17CurrentM31Semantics

abbrev Mul := U32 → U32 → Result U32

def TotalMul (mul : Mul) : Prop := ∀ a b, ∃ z, mul a b = .ok z

def RefinesMul (mul : Mul) : Prop := ∀ a b z, mul a b = .ok z →
  decode z = decode a * decode b

/-- A symbolic range induction proves every emitted squaring iteration and
its exponent; no concrete large exponent/recurrence is normalized. -/
theorem square_loop_total_model (mul : Mul) (htotal : TotalMul mul)
    (href : RefinesMul mul) (iter : Range) (value : field.M31) :
    ∃ out : field.M31, field.square_n_loop mul iter value = .ok out ∧
      decode out = decode value ^ (2 ^ (iter.end.val - iter.start.val)) := by
  induction hfuel : iter.end.val - iter.start.val generalizing iter value with
  | zero =>
    have hge : iter.start.val ≥ iter.end.val := by omega
    have hn := next_done iter hge
    refine ⟨value,?_,?_⟩
    · unfold field.square_n_loop
      rw [loop.eq_def]
      simp only [field.square_n_loop.body,hn,bind_tc_ok]
      rfl
    · simp only [hfuel,pow_zero,pow_one]
  | succ n ih =>
    have hlt : iter.start.val < iter.end.val := by omega
    obtain ⟨iter1,hn,hinc,hend,_⟩ := next_step iter hlt
    obtain ⟨v,hmul⟩ := htotal value value
    have hn1 : iter1.end.val - iter1.start.val = n := by rw [hend,hinc]; omega
    obtain ⟨out,hout,hdecode⟩ := ih iter1 v hn1
    refine ⟨out,?_,?_⟩
    · unfold field.square_n_loop
      rw [loop.eq_def]
      simp only [field.square_n_loop.body,hn,hmul,bind_tc_ok]
      exact hout
    · calc
        decode out = (decode value * decode value) ^ (2^n) := by
          rw [href value value v hmul] at hdecode
          exact hdecode
        _ = decode value ^ (2*(2^n)) := by rw [pow_mul,pow_two]
        _ = decode value ^ (2^(n+1)) := by rw [pow_succ,Nat.mul_comm 2 (2^n)]

theorem square_n_total_model (mul : Mul) (htotal : TotalMul mul)
    (href : RefinesMul mul) (value : field.M31) (count : Usize) :
    ∃ out : field.M31, field.square_n mul value count = .ok out ∧
      decode out = decode value ^ (2^count.val) := by
  obtain ⟨out,ho,hv⟩ := square_loop_total_model mul htotal href
    {start:=0#usize,«end»:=count} value
  refine ⟨out,ho,?_⟩
  change decode out = decode value ^ (2^(count.val-0)) at hv
  simpa only [Nat.sub_zero] using hv

#print axioms square_loop_total_model
#print axioms square_n_total_model
end AspisR1M31Inverse.SquareProof
