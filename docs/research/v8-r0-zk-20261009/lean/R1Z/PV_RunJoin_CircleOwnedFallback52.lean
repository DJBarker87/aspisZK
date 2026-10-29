import R1Z.PV_RunJoin_CircleOwnedMap52
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleOwnedFallback52
open PV_RunJoin_CircleOwnedCarrier52

def firstParameter : Q := ((0#u32,0#u32),(1#u32,0#u32))
def secondParameter : Q := ((1#u32,0#u32),(1#u32,0#u32))

theorem owned_first : Array.index_usize PV_AL_CircleOwned.FALLBACK 0#usize = ok (encQ firstParameter) := by
  unfold PV_AL_CircleOwned.FALLBACK PV_AL_CircleOwned.aspis_core.field.CM31.ZERO
    PV_AL_CircleOwned.aspis_core.field.CM31.ONE firstParameter encQ encCM
  rfl

theorem owned_second : Array.index_usize PV_AL_CircleOwned.FALLBACK 1#usize = ok (encQ secondParameter) := by
  unfold PV_AL_CircleOwned.FALLBACK PV_AL_CircleOwned.aspis_core.field.CM31.ZERO
    PV_AL_CircleOwned.aspis_core.field.CM31.ONE secondParameter encQ encCM
  rfl

theorem neutral_first : Array.index_usize PV_RunJoin_CircleRawMap52.FALLBACK 0#usize = ok firstParameter := rfl

theorem neutral_second : Array.index_usize PV_RunJoin_CircleRawMap52.FALLBACK 1#usize = ok secondParameter := rfl

theorem first : PV_AL_CircleOwned.fallback 0#usize = (do
    let p ← PV_RunJoin_CircleRawMap52.fallback 0#usize
    ok (encPoint p)) := by
  unfold PV_AL_CircleOwned.fallback PV_RunJoin_CircleRawMap52.fallback
  change (do
      let q ← Array.index_usize PV_AL_CircleOwned.FALLBACK 0#usize
      let r ← PV_AL_CircleOwned.map_parameter q
      match r with
      | .Ok p => ok p
      | .Err _ => ok {x:=PV_AL_CircleOwned.aspis_core.field.QM31.ONE,y:=PV_AL_CircleOwned.aspis_core.field.QM31.ZERO}) = _
  rw [owned_first,neutral_first]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_CircleOwnedMap52.complete]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r _
  cases r with
  | Ok p => rfl
  | Err e => cases e <;> rfl

theorem second : PV_AL_CircleOwned.fallback 1#usize = (do
    let p ← PV_RunJoin_CircleRawMap52.fallback 1#usize
    ok (encPoint p)) := by
  unfold PV_AL_CircleOwned.fallback PV_RunJoin_CircleRawMap52.fallback
  change (do
      let q ← Array.index_usize PV_AL_CircleOwned.FALLBACK 1#usize
      let r ← PV_AL_CircleOwned.map_parameter q
      match r with
      | .Ok p => ok p
      | .Err _ => ok {x:=PV_AL_CircleOwned.aspis_core.field.QM31.ONE,y:=PV_AL_CircleOwned.aspis_core.field.QM31.ZERO}) = _
  rw [owned_second,neutral_second]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_CircleOwnedMap52.complete]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r _
  cases r with
  | Ok p => rfl
  | Err e => cases e <;> rfl

#print axioms firstParameter
#print axioms secondParameter
#print axioms owned_first
#print axioms owned_second
#print axioms neutral_first
#print axioms neutral_second
#print axioms first
#print axioms second
end R1Z.PV_RunJoin_CircleOwnedFallback52
