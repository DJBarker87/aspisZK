import R1Z.PV_Join_ParseScalarCanonical5
import R1Z.PV_Join_ResultInvariant5
set_option autoImplicit false
namespace R1Z.PV_Join_ParseComplexCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5
abbrev SM (o : Option aspis_core.field.M31) := ∀ x, o = some x → M x
abbrev SC (o : Option aspis_core.field.CM31) := ∀ x, o = some x → C x

theorem scalar (bytes : Array U8 4#usize) :
    Safe SM (ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes bytes) := by
  intro o ho x hx
  subst o
  exact PV_Join_ParseScalarCanonical5.parsed bytes x ho

theorem complex (bytes : Slice U8) :
    Safe SC (ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes bytes) := by
  unfold ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes
  apply bind_any; intro s
  apply bind_any; intro r
  cases r with
  | Err e => apply PV_Join_ResultInvariant5.ok; intro x hx; cases hx
  | Ok value =>
    apply bind SM SC _ _ (scalar value)
    intro o ho
    cases o with
    | none =>
      simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
        bind_tc_ok]
      apply bind_any; intro _
      apply PV_Join_ResultInvariant5.ok
      intro x hx; cases hx
    | some a =>
      simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
      apply bind_any; intro s1
      apply bind_any; intro r1
      cases r1 with
      | Err e => apply PV_Join_ResultInvariant5.ok; intro x hx; cases hx
      | Ok value1 =>
        apply bind SM SC _ _ (scalar value1)
        intro o1 ho1
        cases o1 with
        | none =>
          simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
            bind_tc_ok]
          apply bind_any; intro _
          apply PV_Join_ResultInvariant5.ok
          intro x hx; cases hx
        | some b =>
          simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
          apply PV_Join_ResultInvariant5.ok
          intro x hx
          cases hx
          exact ⟨ho a rfl,ho1 b rfl⟩

#print axioms scalar
#print axioms complex
end R1Z.PV_Join_ParseComplexCanonical5
