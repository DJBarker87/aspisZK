import R1Z.ProverCommitInverseCases51

/-! V380 inversion subset: actual extracted QM31 inverse and subtraction.
The LogUp caller's no-pole premise is explicit; native caller association,
WideExact and generic CodeField inversion paths are not inferred here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_InversionQ
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open ProverCommitNativeQ48 (source)

/-- This is the actual zero test evaluated before the extracted norm chain.
On canonical nonzero operands it always returns the same branch outcome. -/
theorem branch_nonzero (operand : Old.Q) (canonical : Canonical operand)
    (nonzero : decode operand ≠ 0) :
    field.QM31.is_zero (source operand) = ok false := by
  have hn : operand ≠ zero := by
    intro hz
    exact nonzero ((ProverCommitNativeQInverse49.zero_iff operand canonical).mpr hz)
  rw [ProverCommitNativeQInverse49.zero_test]
  simp only [hn,decide_false]

/-- The helper at logup.rs:199/212 inverts chi-slot. A canonical non-pole
pair has a canonical actual-source subtraction result, a false zero branch,
and a successful extracted inverse. This is not just an implication FROM
successful inversion. -/
theorem logup_operand (chi slot : Old.Q) (hchi : Canonical chi)
    (hslot : Canonical slot) (noPole : decode chi ≠ decode slot) :
    ∃ operand inverse : Old.Q,
      field.QM31.sub (source chi) (source slot) = ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧
      field.QM31.is_zero (source operand) = ok false ∧
      kernels.inverse_q (source operand) = ok (some (source inverse)) ∧
      Canonical inverse := by
  obtain ⟨operand,hs,hc,hv⟩ := ProverCommitNativeQ48.sub chi slot hchi hslot
  have hn : decode operand ≠ 0 := by rw [hv]; exact sub_ne_zero.mpr noPole
  obtain ⟨inverse,hi,hci,_⟩ := ProverCommitNativeQInverse49.inverse operand hc hn
  exact ⟨operand,inverse,hs,hc,hn,branch_nonzero operand hc hn,hi,hci⟩

/-- Per-site aggregation permits all reached/rejected-attempt operands;
there is no acceptance or P_R1-success restriction. The source-to-site
enumeration and no-pole guard must still be proved for the actual caller. -/
theorem logup_all (chi : Old.Q) (slots : List Old.Q) (hchi : Canonical chi)
    (canonical : ∀ slot ∈ slots, Canonical slot)
    (noPole : ∀ slot ∈ slots, decode chi ≠ decode slot) :
    ∀ slot ∈ slots, ∃ operand inverse : Old.Q,
      field.QM31.sub (source chi) (source slot) = ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧
      field.QM31.is_zero (source operand) = ok false ∧
      kernels.inverse_q (source operand) = ok (some (source inverse)) ∧
      Canonical inverse := by
  intro slot member
  exact logup_operand chi slot hchi (canonical slot member) (noPole slot member)

theorem zero_exact (operand : Old.Q) (canonical : Canonical operand) :
    kernels.inverse_q (source operand) = ok none ↔ decode operand = 0 :=
  ProverCommitInverseCases51.none_iff operand canonical

#print axioms branch_nonzero
#print axioms logup_operand
#print axioms logup_all
#print axioms zero_exact
end R1Z.PV_L2_InversionQ
