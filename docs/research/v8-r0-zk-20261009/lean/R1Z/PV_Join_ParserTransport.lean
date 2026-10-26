import R1Z.ProverRwSuccessParserSource
import R1Z.PV_CB_Op71Funs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_ParserTransport
open Aeneas Aeneas.Std Result ProverRwFull
def decodeC (x : PV_CB_ShippedOp71.aspis_core.field.CM31) : aspis_core.field.CM31 := ⟨x.a,x.b⟩
def decode (x : PV_CB_ShippedOp71.aspis_core.field.QM31) : aspis_core.field.QM31 := ⟨decodeC x.c0,decodeC x.c1⟩

theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (same : ∀ value, f value = g value) : (r >>= f) = (r >>= g) := by
  cases r with
  | ok value => exact same value
  | fail error => rfl
  | div => rfl

theorem scalar (bytes : Array U8 4#usize) :
    PV_CB_ShippedOp71.aspis_core.field.M31.from_le_bytes bytes =
      ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes bytes := by
  unfold PV_CB_ShippedOp71.aspis_core.field.M31.from_le_bytes
    ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes
    PV_CB_ShippedOp71.aspis_core.field.P
    ProverRwSuccessParserSource.aspis_core.field.P
    ProverRwDictionaryBytesSource.aspis_core.field.P
  rfl

/-- Structural Result/Option transport, including all short-input failures. -/
theorem complex (bytes : Slice U8) :
    (do let value ← PV_CB_ShippedOp71.aspis_core.field.CM31.from_le_bytes bytes
        ok (value.map decodeC)) =
      ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes bytes := by
  simp only [PV_CB_ShippedOp71.aspis_core.field.CM31.from_le_bytes,
    ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes,scalar,
    PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_assoc_eq,bind_tc_ok]
  apply bind_congr
  intro firstSlice
  apply bind_congr
  intro firstArray
  cases firstArray with
  | Err error => rfl
  | Ok firstWord =>
    simp only [bind_assoc_eq]
    apply bind_congr
    intro firstOption
    cases firstOption with
    | none => simp [massert,Option.map]
    | some a =>
      simp only [bind_tc_ok,bind_assoc_eq]
      apply bind_congr
      intro secondSlice
      apply bind_congr
      intro secondArray
      cases secondArray with
      | Err error => rfl
      | Ok secondWord =>
        simp only [bind_assoc_eq]
        apply bind_congr
        intro secondOption
        cases secondOption <;> simp [massert,Option.map,decodeC]

theorem quartic (bytes : Slice U8) :
    (do let value ← PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes bytes
        ok (value.map decode)) =
      ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes := by
  unfold PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
  simp_rw [← complex]
  simp only [PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_assoc_eq,bind_tc_ok]
  apply bind_congr
  intro firstSlice
  apply bind_congr
  intro firstOption
  cases firstOption with
  | none => simp [massert,Option.map]
  | some a =>
    simp only [bind_tc_ok,Option.map,bind_assoc_eq]
    apply bind_congr
    intro secondSlice
    apply bind_congr
    intro secondOption
    cases secondOption <;> simp [massert,Option.map,decode,decodeC]

#print axioms bind_congr
#print axioms scalar
#print axioms complex
#print axioms quartic
end R1Z.PV_Join_ParserTransport
