import R1Z.ProverRwDictionaryLayout
import R1Z.ProverRwDictionaryDerivedSource
import AspisR1ProverMaterial14.Funs
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryDerived
open Aeneas Aeneas.Std Result ProverRwFull
attribute [local instance] Classical.propDecidable
abbrev mEq := ProverRwDictionaryDerivedSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
abbrev cEq := ProverRwDictionaryDerivedSource.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
abbrev qEq := ProverRwDictionaryDerivedSource.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq

theorem c_status (x y : aspis_core.field.CM31) :
    cEq x y = .ok (decide (x=y)) := by
  cases x with
  | mk a b =>
    cases y with
    | mk c d =>
      by_cases h : a=c <;> by_cases k : b=d <;>
        simp [cEq,ProverRwDictionaryDerivedSource.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
          ProverRwDictionaryDerivedSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,h,k]

theorem q_status (x y : aspis_core.field.QM31) :
    qEq x y = .ok (decide (x=y)) := by
  cases x with
  | mk a b =>
    cases y with
    | mk c d =>
      by_cases h : a=c <;> by_cases k : b=d <;>
        simp [qEq,ProverRwDictionaryDerivedSource.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
          show ∀ u v, ProverRwDictionaryDerivedSource.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq u v =
            .ok (decide (u=v)) from c_status,h,k]

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryLayout.selected ops with
    op53 := AspisR1ProverMaterial14.aspis_core.field.M31.Insts.CoreCloneClone.clone
    op54 := mEq
    op62 := ProverRwDictionaryDerivedSource.aspis_core.field.QM31.Insts.CoreCloneClone.clone
    op63 := qEq}

theorem m_clone (ops : ExternalFuns) (x : U32) : (selected ops).op53 x = .ok x := rfl

theorem m_eq (ops : ExternalFuns) (x y : U32) :
    (selected ops).op54 x y = .ok (decide (x=y)) := rfl

theorem q_clone (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (selected ops).op62 x = .ok x := rfl

theorem q_eq (ops : ExternalFuns) (x y : aspis_core.field.QM31) :
    (selected ops).op63 x y = .ok (decide (x=y)) := q_status x y

#print axioms c_status
#print axioms q_status
#print axioms m_clone
#print axioms m_eq
#print axioms q_clone
#print axioms q_eq
end R1Z.ProverRwDictionaryDerived
