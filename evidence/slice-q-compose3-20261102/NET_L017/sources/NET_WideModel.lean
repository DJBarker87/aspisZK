import NEO_WideTotal
import NEO_FieldView
import NET_ParserComposed
set_option autoImplicit false
namespace NET_WideModel
open Aeneas Aeneas.Std Result AspisR1
open S8OwnedP6FieldParserTransport
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact

def recover (w : Array U32 8#usize) : E :=
 LPf_WideConstruction.value (w.val[0]?.getD 0#u32) (w.val[1]?.getD 0#u32)
  (w.val[2]?.getD 0#u32) (w.val[3]?.getD 0#u32)
  (w.val[4]?.getD 0#u32) (w.val[5]?.getD 0#u32)
  (w.val[6]?.getD 0#u32) (w.val[7]?.getD 0#u32)

theorem roundtrip (x : E) : recover (NEB_ArrayRefs.wordsE x)=x := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 rfl

def wide (bytes : Slice U8) : Result (Option E) :=
 mapResult (Option.map recover) (NEO_WindowV2.wide bytes)

/-- All lengths and all rejection prefixes, with the complete nominal carrier. -/
theorem result (bytes : Slice U8) :
 wide bytes=FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes := by
 unfold wide
 rw [NEO_WideTotal.result]
 unfold NEO_WideTotal.cohort
 cases h:FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes with
 | ok o =>
  cases o with
  | none => rfl
  | some x =>
   simp only [bind_tc_ok,NBG_WideCarriers.to_limbs_result,mapResult,Option.map]
   change ok (some (recover (NEB_ArrayRefs.wordsE x)))=ok (some x)
   rw [roundtrip]
 | fail e => rfl
 | div => rfl

theorem result_state_effects {S Event : Type} (state : S) (bytes : Slice U8) :
 NEB_PureFrame.run (Event:=Event) state (wide bytes)=
 NEB_PureFrame.run state (FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes) := by
 rw [result]

#print axioms roundtrip
#print axioms result
#print axioms result_state_effects
end NET_WideModel
