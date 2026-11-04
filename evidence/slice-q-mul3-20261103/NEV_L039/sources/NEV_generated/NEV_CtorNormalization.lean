import NEV_AccumulateCallees
set_option autoImplicit false
noncomputable section
namespace NEV_CtorNormalization
open Aeneas Aeneas.Std Result
abbrev Q := NEV_CodeFieldRaw.aspis_core.field.QM31

def normalized (q : Q) : Q :=
 ⟨⟨AspisS1M31Embedding.Total.reduce q.c0.a,AspisS1M31Embedding.Total.reduce q.c0.b⟩,
  ⟨AspisS1M31Embedding.Total.reduce q.c1.a,AspisS1M31Embedding.Total.reduce q.c1.b⟩⟩
def Canonical (q : Q) : Prop :=
 (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
 (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647)
/-- Nominal constructor transport only; each remainder uses the retained
all-machine-word S1 law, rather than a new arithmetic proof. -/
theorem total (q : Q) :
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31 q=ok (normalized q) := by
  simp only [NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    NEV_CodeFieldBridge.rem,bind_tc_ok,normalized]
theorem reduce_identity (word : U32) (small : word.val<2147483647) :
    AspisS1M31Embedding.Total.reduce word=word := by
  apply UScalar.eq_of_val_eq
  rw [AspisS1M31Embedding.Total.reduce_val]
  exact Nat.mod_eq_of_lt small
theorem identity (q : Q) (canonical : Canonical q) : normalized q=q := by
  simp only [normalized,reduce_identity q.c0.a canonical.1.1,
    reduce_identity q.c0.b canonical.1.2,reduce_identity q.c1.a canonical.2.1,
    reduce_identity q.c1.b canonical.2.2]

/-- Equality to the adopted row callback on the SAME canonical read value. -/
theorem cohort (ops : AspisR1.Port3_NativeQueryBody.Ops)
    (q : NEV_AccumulateCarriers.RawQ)
    (canonical : Canonical (NEV_AccumulateRaw.NEV_Bindings.toCtorQ q)) :
    (do let e ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31 q
        ok (NEV_AccumulateCarriers.toE e)) =
      (NBF_RowInstall.install ops).op1 (NEV_AccumulateCarriers.toQ q) := by
  simp only [NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    total,identity _ canonical,bind_tc_ok,NEV_CodeFieldRaw.aspis_core.field.QM31.ZERO]
  rfl

#print axioms total
#print axioms reduce_identity
#print axioms identity
#print axioms cohort
end NEV_CtorNormalization
end
