import PoolW_ZeroArithmetic
set_option autoImplicit false
namespace AspisR1.PoolW_ZeroExact
open Aeneas Aeneas.Std Result ControlFlow WP

def remaining (bytes : Slice U8) (i : Usize) (zero : Bool) : Bool :=
  zero && (bytes.val.drop i.val).all (fun byte => decide (byte = 0#u8))

def Inv (bytes : Slice U8) (target : Bool) (s : Usize × Bool) : Prop :=
  s.1.val ≤ bytes.val.length ∧ remaining bytes s.1 s.2 = target

theorem loop_exact (bytes : Slice U8) (i : Usize) (zero : Bool)
    (bound : i.val ≤ bytes.val.length) :
    PoolW_Zero.zero_bytes_loop bytes i zero = ok (remaining bytes i zero) := by
  let target := remaining bytes i zero
  have h : WP.spec (PoolW_Zero.zero_bytes_loop bytes i zero) (fun out => out = target) := by
    unfold PoolW_Zero.zero_bytes_loop
    refine loop.spec_decr_nat
      (fun s : Usize × Bool => bytes.val.length - s.1.val)
      (Inv bytes target) (fun out : Bool => out = target)
      (fun (j,z) => PoolW_Zero.zero_bytes_loop.body bytes j z)
      (i,zero) ?_ ⟨bound,rfl⟩
    rintro ⟨j,z⟩ ⟨range,eq⟩
    dsimp only at range eq ⊢
    by_cases more : j < Slice.len bytes
    · cases z with
      | false =>
        rw [PoolW_ZeroStep.stopped_false]
        change false = target
        simpa [remaining] using eq
      | true =>
        have valid : j.val < bytes.val.length := by scalar_tac
        have read : Slice.index_usize bytes j = ok (bytes.val[j.val]'valid) := by
          simp [Slice.index_usize,Slice.getElem?_Usize_eq,valid]
        rw [PoolW_ZeroStep.step bytes j _ more read]
        change (Inv bytes target (Usize.wrapping_add j 1#usize,_) ∧
          bytes.val.length - (Usize.wrapping_add j 1#usize).val < bytes.val.length - j.val)
        have inc := PoolW_ZeroArithmetic.increment bytes j more
        refine ⟨⟨?_,?_⟩,?_⟩
        · simp only [inc]; omega
        · unfold remaining at eq ⊢
          simp only [inc]
          have dropped := List.drop_eq_getElem_cons valid
          simpa only [dropped,List.all_cons,Bool.true_and] using eq
        · simp only [inc]; omega
    · rw [PoolW_ZeroStep.exhausted bytes j more z]
      change z = target
      have ended : bytes.val.drop j.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      simpa [remaining,ended] using eq
  cases run : PoolW_Zero.zero_bytes_loop bytes i zero with
  | fail e => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    rw [h]

theorem exact (bytes : Slice U8) :
    PoolW_Zero.zero_bytes bytes = ok (bytes.val.all (fun byte => decide (byte = 0#u8))) := by
  simpa [PoolW_Zero.zero_bytes,remaining] using loop_exact bytes 0#usize true (by simp)

#print axioms loop_exact
#print axioms exact
end AspisR1.PoolW_ZeroExact
