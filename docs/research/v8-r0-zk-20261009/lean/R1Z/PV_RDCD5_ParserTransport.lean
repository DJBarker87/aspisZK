import R1Z.PV_RDCD5_ParserFlat
import R1Z.ProverRwSuccessParserSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_ParserTransport
open Aeneas Aeneas.Std Result PV_RDCD4_BytesSource

theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (same : ∀ a, f a = g a) : (r >>= f) = (r >>= g) := by
  cases r with
  | ok a => exact same a
  | fail e => rfl
  | div => rfl

theorem range_bind {T B : Type} (s : Slice T) (a b : Usize)
    (g : List T → Result B) :
    (do let out ← core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice T) s {start:=a, «end»:=b}
        g out.val) = (PV_RDCD5_ParserRange.index s.val a.val b.val >>= g) := by
  rw [← PV_RDCD5_ParserRange.binding s a b]
  simp only [bind_assoc_eq,bind_tc_ok]

theorem scalar (bytes : Array U8 4#usize) :
    ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes bytes =
      ok (PV_RDCD4_BytesSource.scalar bytes) := by
  rw [scalar_binding]
  unfold ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes
    ProverRwSuccessParserSource.aspis_core.field.P
    ProverRwDictionaryBytesSource.aspis_core.field.P
    PV_RDCD4_FieldSource.aspis_core.field.P
  rfl

/-- One source component, retaining its range panic, conversion Err and None. -/
def nativeComponent (bytes : Slice U8) (a b : Usize) : Result (Option M) := do
  let part ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=a, «end»:=b}
  let converted ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 part
  match converted with
  | .Err _ => ok none
  | .Ok value => ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes value

theorem convert_component (part : Slice U8) :
    (do let converted ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 part
        match converted with
        | .Err _ => ok none
        | .Ok value => ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes value) =
      (match PV_RDCD4_TryArray194.into 4#usize part.val with
       | none => ok none
       | some value => ok (PV_RDCD4_BytesSource.scalar value)) := by
  simp only [core.array.TryFromArrayCopySlice.try_from,PV_RDCD4_TryArray194.into,Slice.length]
  split <;> simp only [↓reduceDIte,bind_tc_ok,scalar]

theorem component_binding (bytes : Slice U8) (a b : Usize) :
    nativeComponent bytes a b = component bytes.val a.val b.val := by
  unfold nativeComponent component
  simp_rw [convert_component]
  exact range_bind bytes a b _

theorem complex_shape (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes bytes =
      (do let a ← nativeComponent bytes 0#usize 4#usize
          match a with
          | none => ok none
          | some a => do
            let b ← nativeComponent bytes 4#usize 8#usize
            match b with
            | none => ok none
            | some b => ok (some (⟨a,b⟩ : C))) := by
  unfold ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes nativeComponent
  simp only [bind_assoc_eq,bind_tc_ok]
  apply bind_congr
  intro firstSlice
  apply bind_congr
  intro firstArray
  cases firstArray with
  | Err e => rfl
  | Ok firstWord =>
    simp only [bind_assoc_eq]
    apply bind_congr
    intro firstOption
    cases firstOption with
    | none => simp [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,massert]
    | some a =>
      simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
      apply bind_congr
      intro secondSlice
      apply bind_congr
      intro secondArray
      cases secondArray with
      | Err e => rfl
      | Ok secondWord =>
        simp only [bind_assoc_eq]
        apply bind_congr
        intro secondOption
        cases secondOption <;> simp [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,massert]

theorem complex (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes bytes = cm bytes.val := by
  rw [complex_shape,component_binding,component_binding]
  rfl

/-- Arbitrary input slices and whole Result: panic, None and Some all retained. -/
theorem quartic (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes = qm bytes.val := by
  unfold ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes qm
  simp_rw [complex]
  simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_assoc_eq,bind_tc_ok]
  rw [← range_bind bytes 0#usize 8#usize]
  apply bind_congr
  intro firstSlice
  apply bind_congr
  intro firstOption
  cases firstOption with
  | none => simp [massert]
  | some c0 =>
    simp only [bind_tc_ok]
    rw [← range_bind bytes 8#usize 16#usize]
    apply bind_congr
    intro secondSlice
    apply bind_congr
    intro secondOption
    cases secondOption <;> simp [massert]

#print axioms bind_congr
#print axioms range_bind
#print axioms scalar
#print axioms convert_component
#print axioms component_binding
#print axioms complex_shape
#print axioms complex
#print axioms quartic
end R1Z.PV_RDCD5_ParserTransport
