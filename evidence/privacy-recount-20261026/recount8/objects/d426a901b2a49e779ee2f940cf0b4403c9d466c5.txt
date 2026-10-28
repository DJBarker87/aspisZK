import R1Z.ProverCommitPowers48
/-! Successful complete gamma and kappa arrays, with exact field powers.
All inputs are full-width canonical source values; no power-array equality
is supplied as a hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitGamma48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitPowers48

def zero : Raw := (ProverCommitSubfieldOps47.zero,ProverCommitSubfieldOps47.zero)
def one : Raw := (ProverCommitSubtraction47.one,ProverCommitSubfieldOps47.zero)

theorem zero_canonical : canonical zero :=
  ⟨ProverCommitSubfieldOps47.zero_canonical,ProverCommitSubfieldOps47.zero_canonical⟩
theorem one_canonical : canonical one :=
  ⟨ProverCommitSubtraction47.one_canonical,ProverCommitSubfieldOps47.zero_canonical⟩
theorem zero_value : value zero=0 := rfl
theorem one_value : value one=1 := rfl

theorem source_zero : field.wide_exact.WideExact.ZERO=source zero := by
  simp only [field.wide_exact.WideExact.ZERO,field.QM31.ZERO,source,pack,
    ProverCommitRelease47.convE,ProverCommitRelease47.convQ,ProverCommitRelease47.convC,
    ProverCommitPrimitive47.fromQ,ProverCommitPrimitive47.fromC,zero,ProverCommitSubfieldOps47.zero]

theorem source_one : field.wide_exact.WideExact.ONE=source one := by
  simp only [field.wide_exact.WideExact.ONE,field.QM31.ONE,field.QM31.ZERO,source,pack,
    ProverCommitRelease47.convE,ProverCommitRelease47.convQ,ProverCommitRelease47.convC,
    ProverCommitPrimitive47.fromQ,ProverCommitPrimitive47.fromC,one,
    ProverCommitSubfieldOps47.zero,ProverCommitSubtraction47.one]

theorem repeat_zero (size : Usize) : Array.repeat size field.wide_exact.WideExact.ZERO=
    sourceArray size (fun _ => zero) := by
  rw [source_zero]
  apply Subtype.ext
  simp only [Array.repeat,sourceArray,List.ofFn_const]

theorem gamma_exact (x : Raw) (hx : canonical x) :
    ∃ ys : Nat → Raw, gamma (source x)=ok (sourceArray 29#usize ys) ∧
      (∀ k, k < 29 → canonical (ys k)) ∧ ∀ k, k < 29 → value (ys k)=(value x)^k := by
  obtain ⟨ys,hy,hcy,hval⟩ := fill_value 29#usize (by decide) (fun _ => zero)
    (fun _ _ => zero_canonical) x one hx one_canonical 29 29#u8 rfl 0#usize (by scalar_tac)
  refine ⟨ys,?_,hcy,?_⟩
  · rw [gamma,repeat_zero,source_one]
    exact hy
  · intro k hk
    have h := hval k hk
    change value (ys k)=(if 0 ≤ k ∧ k < 0+29 then value one*value x^(k-0) else value zero) at h
    rw [if_pos (by omega)] at h
    simpa only [one_value,one_mul,Nat.sub_zero] using h

theorem kappa_exact (x : Raw) (hx : canonical x) :
    ∃ ys : Nat → Raw, kappa (source x)=ok (sourceArray 7#usize ys) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧ ∀ k, k < 7 → value (ys k)=(value x)^k := by
  obtain ⟨ys,hy,hcy,hval⟩ := fill_value 7#usize (by decide) (fun _ => zero)
    (fun _ _ => zero_canonical) x one hx one_canonical 7 7#u8 rfl 0#usize (by scalar_tac)
  refine ⟨ys,?_,hcy,?_⟩
  · rw [kappa,repeat_zero,source_one]
    exact hy
  · intro k hk
    have h := hval k hk
    change value (ys k)=(if 0 ≤ k ∧ k < 0+7 then value one*value x^(k-0) else value zero) at h
    rw [if_pos (by omega)] at h
    simpa only [one_value,one_mul,Nat.sub_zero] using h

#print axioms zero_canonical
#print axioms one_canonical
#print axioms zero_value
#print axioms one_value
#print axioms source_zero
#print axioms source_one
#print axioms repeat_zero
#print axioms gamma_exact
#print axioms kappa_exact
end R1Z.ProverCommitGamma48
