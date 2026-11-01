import R1Z.PV_RunJoin_MaskScalarTotal69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskFieldTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117
abbrev C := aspis_core.field.CM31
abbrev Q := aspis_core.field.QM31

theorem cadd (a b : C) : ∃ c,aspis_core.field.CM31.add a b=ok c := by
  unfold aspis_core.field.CM31.add
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact ⟨_,rfl⟩

theorem csub (a b : C) : ∃ c,aspis_core.field.CM31.sub a b=ok c := by
  unfold aspis_core.field.CM31.sub
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact ⟨_,rfl⟩

theorem cmul (a b : C) : ∃ c,aspis_core.field.CM31.mul a b=ok c := by
  unfold aspis_core.field.CM31.mul
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact ⟨_,rfl⟩

theorem csquare (a : C) : ∃ c,aspis_core.field.CM31.square a=ok c := by
  unfold aspis_core.field.CM31.square
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact ⟨_,rfl⟩

theorem cscale (a : C) (b : U32) : ∃ c,aspis_core.field.CM31.mul_m31 a b=ok c := by
  unfold aspis_core.field.CM31.mul_m31
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact ⟨_,rfl⟩

theorem cdouble (a : C) : ∃ c,aspis_core.field.CM31.double a=ok c := by
  unfold aspis_core.field.CM31.double
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact ⟨_,rfl⟩

theorem mulR (a : C) : ∃ c,aspis_core.field.mul_by_r a=ok c := by
  unfold aspis_core.field.mul_by_r
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cdouble _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact cdouble _
    | exact ⟨_,rfl⟩

theorem qadd (a b : Q) : ∃ c,aspis_core.field.QM31.add a b=ok c := by
  unfold aspis_core.field.QM31.add
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cdouble _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (mulR _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact cdouble _
    | exact mulR _
    | exact ⟨_,rfl⟩

theorem qmul (a b : Q) : ∃ c,aspis_core.field.QM31.mul a b=ok c := by
  unfold aspis_core.field.QM31.mul
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cdouble _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (mulR _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qadd _ _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact cdouble _
    | exact mulR _
    | exact qadd _ _
    | exact ⟨_,rfl⟩

theorem qsquare (a : Q) : ∃ c,aspis_core.field.QM31.square a=ok c := by
  unfold aspis_core.field.QM31.square
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cdouble _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (mulR _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qmul _ _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact cdouble _
    | exact mulR _
    | exact qadd _ _
    | exact qmul _ _
    | exact ⟨_,rfl⟩

theorem qscale (a : Q) (b : U32) : ∃ c,aspis_core.field.QM31.mul_m31 a b=ok c := by
  unfold aspis_core.field.QM31.mul_m31
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cdouble _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (mulR _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qsquare _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact cdouble _
    | exact mulR _
    | exact qadd _ _
    | exact qmul _ _
    | exact qsquare _
    | exact ⟨_,rfl⟩

theorem hostR (a : C) : ∃ c,host_arithmetic.cm31_mul_r a=ok c := by
  unfold host_arithmetic.cm31_mul_r
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cdouble _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (mulR _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qsquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qscale _ _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact cdouble _
    | exact mulR _
    | exact qadd _ _
    | exact qmul _ _
    | exact qsquare _
    | exact qscale _ _
    | exact ⟨_,rfl⟩

theorem hostI (a : C) : ∃ c,host_arithmetic.cm31_mul_i a=ok c := by
  unfold host_arithmetic.cm31_mul_i
  repeat' first
    | progress simp only [lift,bind_tc_ok]
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.add _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.sub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.mul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.reduce _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.neg _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (PV_RunJoin_MaskScalarTotal69.double _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csub _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (csquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (cdouble _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (mulR _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qadd _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qmul _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qsquare _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (qscale _ _); intro _)
    | (apply ProverRwP6BindTotal.bind_total _ _ (hostR _); intro _)
  first
    | exact PV_RunJoin_MaskScalarTotal69.add _ _
    | exact PV_RunJoin_MaskScalarTotal69.sub _ _
    | exact PV_RunJoin_MaskScalarTotal69.mul _ _
    | exact PV_RunJoin_MaskScalarTotal69.reduce _
    | exact PV_RunJoin_MaskScalarTotal69.neg _
    | exact PV_RunJoin_MaskScalarTotal69.double _
    | exact cadd _ _
    | exact csub _ _
    | exact cmul _ _
    | exact csquare _
    | exact cscale _ _
    | exact cdouble _
    | exact mulR _
    | exact qadd _ _
    | exact qmul _ _
    | exact qsquare _
    | exact qscale _ _
    | exact hostR _
    | exact ⟨_,rfl⟩

#print axioms cadd
#print axioms csub
#print axioms cmul
#print axioms csquare
#print axioms cscale
#print axioms cdouble
#print axioms mulR
#print axioms qadd
#print axioms qmul
#print axioms qsquare
#print axioms qscale
#print axioms hostR
#print axioms hostI
end R1Z.PV_RunJoin_MaskFieldTotal69
