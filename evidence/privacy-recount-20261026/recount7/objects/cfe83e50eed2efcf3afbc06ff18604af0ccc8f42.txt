import R1Z.PV_Join_ParseComplexCanonical5
set_option autoImplicit false
namespace R1Z.PV_Join_ParseQuarticCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5
open PV_Join_ParseComplexCanonical5
abbrev SQ (o : Option aspis_core.field.QM31) := ∀ x, o = some x → Q x

theorem none_residual {α : Type} (p : α → Prop) :
    Safe (fun o : Option α => ∀ x, o = some x → p x)
      (ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual α none) := by
  unfold ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  apply bind_any; intro _
  apply PV_Join_ResultInvariant5.ok
  intro x hx; cases hx

theorem quartic (bytes : Slice U8) :
    Safe SQ (ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes) := by
  unfold ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
  apply bind_any; intro s
  apply bind SC SQ _ _ (complex s)
  intro o ho
  cases o with
  | none =>
    simpa only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok] using none_residual Q
  | some a =>
    simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
    apply bind_any; intro s1
    apply bind SC SQ _ _ (complex s1)
    intro o1 ho1
    cases o1 with
    | none =>
      simpa only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok] using none_residual Q
    | some b =>
      simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
      apply PV_Join_ResultInvariant5.ok
      intro x hx
      cases hx
      exact ⟨ho a rfl,ho1 b rfl⟩

#print axioms none_residual
#print axioms quartic
end R1Z.PV_Join_ParseQuarticCanonical5
