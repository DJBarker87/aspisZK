import R1Z.PV_CB3_StagedNativeLink
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedNormalize
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_StagedNativeLink
abbrev normalized := ProverRwSuccessNativeNormalize.normalized

def CanonicalQ (q : aspis_core.field.QM31) : Prop :=
  (q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647) ∧
  (q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647)

theorem source (q : aspis_core.field.QM31) : F.canonical q = ok (normalized q) := by
  rw [PV_CB3_StagedNativeLink.canonical]
  exact ProverRwSuccessNativeNormalize.native q

theorem constructor (a b : aspis_core.field.QM31) :
    F.construct a b = ok {c0 := normalized a,c1 := normalized b} := by
  simp only [F.construct,PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new,
    source,bind_tc_ok]

theorem word_fixed (x : U32) (h : x.val < 2147483647) :
    ProverCommitNativeOps47.normalizeWord x = x := by
  apply UScalar.eq_of_val_eq
  rw [ProverCommitNativeOps47.normalize_val,Nat.mod_eq_of_lt h]

theorem fixed (q : aspis_core.field.QM31) (h : CanonicalQ q) : F.canonical q = ok q := by
  rw [source]
  congr 1
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
  simp only [normalized,ProverRwSuccessNativeNormalize.normalized,
    word_fixed a ha,word_fixed b hb,word_fixed c hc,word_fixed d hd]

theorem constructor_fixed (a b : aspis_core.field.QM31) (ha : CanonicalQ a) (hb : CanonicalQ b) :
    F.construct a b = ok {c0 := a,c1 := b} := by
  simp only [F.construct,PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new,
    fixed a ha,fixed b hb,bind_tc_ok]
#print axioms source
#print axioms constructor
#print axioms word_fixed
#print axioms fixed
#print axioms constructor_fixed
#print axioms ProverRwSuccessNativeNormalize.native
end R1Z.PV_CB3_StagedNormalize
