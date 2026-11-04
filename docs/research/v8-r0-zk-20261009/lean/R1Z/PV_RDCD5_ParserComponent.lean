import R1Z.PV_RDCD5_ParserFlat
import R1Z.ProverRwSuccessParserSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_ParserComponent
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
  simp only [lift,bind_tc_ok]
  split <;> rfl

/-- Decode the conversion result with its exact, explicit nominal carrier. -/
def decodeArray (converted : core.result.Result (Array U8 4#usize)
    core.array.TryFromSliceError) : Result (Option M) :=
  match converted with
  | .Err _ => ok none
  | .Ok value => ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes value

/-- One source component, retaining its range panic, conversion Err and None. -/
def nativeComponent (bytes : Slice U8) (a b : Usize) : Result (Option M) := do
  let part ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=a, «end»:=b}
  let converted ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 part
  decodeArray converted

theorem convert_component (part : Slice U8) :
    (core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 part >>= decodeArray) =
      (let converted : Option (Array U8 4#usize) :=
         PV_RDCD4_TryArray194.into (T := U8) 4#usize part.val
       match converted with
       | Option.none => ok (Option.none : Option M)
       | Option.some value => ok (PV_RDCD4_BytesSource.scalar value)) := by
  unfold core.array.TryFromArrayCopySlice.try_from PV_RDCD4_TryArray194.into
  by_cases h : part.val.length = (4#usize).val
  · simp only [Slice.length,h,↓reduceDIte,bind_tc_ok,decodeArray,scalar]
  · simp only [Slice.length,h,↓reduceDIte,bind_tc_ok,decodeArray]

theorem component_binding (bytes : Slice U8) (a b : Usize) :
    nativeComponent bytes a b = component bytes.val a.val b.val := by
  unfold nativeComponent component
  calc
    _ = (do let part ← core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=a, «end»:=b}
            let converted : Option (Array U8 4#usize) :=
              PV_RDCD4_TryArray194.into (T := U8) 4#usize part.val
            match converted with
            | Option.none => ok (Option.none : Option M)
            | Option.some value => ok (PV_RDCD4_BytesSource.scalar value)) := by
      apply bind_congr
      intro part
      exact convert_component part
    _ = _ := range_bind bytes a b _

/-- Public law for the actual source residual adapter; its private discriminant
instance is not guessed or replaced by a new model. -/
theorem residual_none (T : Type) :
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      T none = ok none := by
  simp [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    massert, read_discriminant, ProverRwDictionaryOptionSource.optionDiscriminant]

theorem first_bind {B : Type} (bytes : Slice U8) (g : List U8 → Result B) :
    (do let part ← core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=0#usize, «end»:=8#usize}
        g part.val) = (PV_RDCD5_ParserRange.index bytes.val 0 8 >>= g) :=
  range_bind bytes 0#usize 8#usize g

theorem second_bind {B : Type} (bytes : Slice U8) (g : List U8 → Result B) :
    (do let part ← core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=8#usize, «end»:=16#usize}
        g part.val) = (PV_RDCD5_ParserRange.index bytes.val 8 16 >>= g) :=
  range_bind bytes 8#usize 16#usize g

#print axioms bind_congr
#print axioms range_bind
#print axioms scalar
#print axioms convert_component
#print axioms component_binding
#print axioms residual_none
#print axioms first_bind
#print axioms second_bind
end R1Z.PV_RDCD5_ParserComponent
