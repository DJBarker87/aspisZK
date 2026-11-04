import R1Z.PV_RDCD5_ParserComponent
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_ParserTransport
open Aeneas Aeneas.Std Result PV_RDCD4_BytesSource PV_RDCD5_ParserComponent
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
  unfold ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes nativeComponent decodeArray
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
        ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,massert,read_discriminant,
        ProverRwDictionaryOptionSource.optionDiscriminant]
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
          ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,massert,read_discriminant,
        ProverRwDictionaryOptionSource.optionDiscriminant]

theorem complex (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes bytes = cm bytes.val := by
  rw [complex_shape,component_binding,component_binding]
  rfl

/-- Normalize the source's Option ? steps before changing borrowed carriers. -/
theorem quartic_shape (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes =
      (do let left ← core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=0#usize, «end»:=8#usize}
          let c0 ← ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes left
          match c0 with
          | none => ok none
          | some c0 => do
            let right ← core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=8#usize, «end»:=16#usize}
            let c1 ← ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes right
            match c1 with
            | none => ok none
            | some c1 => ok (some (⟨c0,c1⟩ : Q))) := by
  unfold ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
  apply bind_congr
  intro firstSlice
  apply bind_congr
  intro firstOption
  cases firstOption with
  | none => simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      bind_tc_ok,residual_none]
  | some c0 =>
    simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
    apply bind_congr
    intro secondSlice
    apply bind_congr
    intro secondOption
    cases secondOption <;> simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      bind_tc_ok,residual_none]

/-- Arbitrary slices and complete Result: panic, None, Some and late checks. -/
theorem quartic (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes = qm bytes.val := by
  let tail : List U8 → Result (Option Q) := fun left => do
    let c0 ← cm left
    match c0 with
    | none => ok none
    | some c0 => do
      let right ← core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=8#usize, «end»:=16#usize}
      let c1 ← cm right.val
      match c1 with
      | none => ok none
      | some c1 => ok (some ⟨c0,c1⟩)
  calc
    _ = (do let part ← core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=0#usize, «end»:=8#usize}
            tail part.val) := by
      rw [quartic_shape]
      apply bind_congr
      intro firstSlice
      dsimp only [tail]
      rw [complex firstSlice]
      apply bind_congr
      intro firstOption
      cases firstOption with
      | none => rfl
      | some c0 =>
        apply bind_congr
        intro secondSlice
        rw [complex secondSlice]
    _ = (PV_RDCD5_ParserRange.index bytes.val 0 8 >>= tail) := first_bind bytes tail
    _ = qm bytes.val := by
      unfold qm
      apply bind_congr
      intro left
      dsimp only [tail]
      apply bind_congr
      intro firstOption
      cases firstOption with
      | none => rfl
      | some c0 => exact second_bind bytes (fun right => do
          let c1 ← cm right
          match c1 with
          | none => ok none
          | some c1 => ok (some (⟨c0,c1⟩ : Q)))

#print axioms complex_shape
#print axioms complex
#print axioms quartic_shape
#print axioms quartic
end R1Z.PV_RDCD5_ParserTransport
