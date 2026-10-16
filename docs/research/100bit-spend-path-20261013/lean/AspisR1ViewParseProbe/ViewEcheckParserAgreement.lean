import AspisR1ViewParseProbe.CleanParameterizedParse
import AspisR1EcheckCut.Funs

set_option autoImplicit false

namespace AspisR1ViewParseProbe.ViewEcheckParserAgreement
open Aeneas Aeneas.Std Result

abbrev HWide := AspisR1ViewParseProbe.field.wide_exact.WideExact
abbrev EWide := AspisR1EcheckCut.field.wide_exact.WideExact

def wideToEcheck (x : HWide) : EWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_bind {α β γ : Type} (f : β → γ)
    (m : Result α) (k : α → Result β) :
    mapResult f (m >>= k) = (m >>= fun x => mapResult f (k x)) := by
  cases m <;> rfl

theorem mapResult_ite {β γ : Type} (f : β → γ)
    (p : Prop) [Decidable p] (a b : Result β) :
    mapResult f (if p then a else b) =
      if p then mapResult f a else mapResult f b := by
  split <;> rfl

@[simp] theorem mapResult_ok {α β : Type} (f : α → β) (x : α) :
    mapResult f (ok x) = ok (f x) := rfl

theorem from_limbs_agreement (limbs : Array U32 8#usize) :
    mapResult (Option.map wideToEcheck)
      (AspisR1ViewParseProbe.field.wide_exact.WideExact.from_limbs limbs) =
      AspisR1EcheckCut.field.wide_exact.WideExact.from_limbs limbs := by
  unfold AspisR1ViewParseProbe.field.wide_exact.WideExact.from_limbs
    AspisR1EcheckCut.field.wide_exact.WideExact.from_limbs
    AspisR1ViewParseProbe.field.P AspisR1EcheckCut.field.P
  simp only [mapResult_bind, mapResult_ite, mapResult_ok,
    Option.map_none, Option.map_some]
  rfl

theorem from_le_bytes_agreement (bytes : Slice U8) :
    mapResult (Option.map wideToEcheck)
      (AspisR1ViewParseProbe.field.wide_exact.WideExact.from_le_bytes bytes) =
      AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes bytes := by
  unfold AspisR1ViewParseProbe.field.wide_exact.WideExact.from_le_bytes
    AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes
    AspisR1ViewParseProbe.field.wide_exact.WideExact.BYTE_LEN
    AspisR1EcheckCut.field.wide_exact.WideExact.BYTE_LEN
  simp only [mapResult_ite, mapResult_bind, mapResult_ok,
    Option.map_none, from_limbs_agreement]

theorem parsed_wide_transfers (bytes : Slice U8) (w : HWide)
    (h : AspisR1ViewParseProbe.field.wide_exact.WideExact.from_le_bytes bytes =
      ok (some w)) :
    AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes bytes =
      ok (some (wideToEcheck w)) := by
  have hm := congrArg (mapResult (Option.map wideToEcheck)) h
  rw [from_le_bytes_agreement] at hm
  exact hm

#print axioms from_limbs_agreement
#print axioms from_le_bytes_agreement
#print axioms parsed_wide_transfers

end AspisR1ViewParseProbe.ViewEcheckParserAgreement
