import R1Z.PV_OWNL_Scale
set_option autoImplicit false
namespace R1Z.PV_OWNL_HelperSlots
open Aeneas Aeneas.Std
open PV_OWNK_TowerCanon PV_OWNL_Scale
attribute [local irreducible] PV_B2_FieldValue.aspis_core.field.QM31.add
 PV_B2_FieldValue.aspis_core.field.QM31.sub
/-- Values and weights are arbitrary; no canonicality assumption on inverse. -/
structure Slot where
 weight : U32
 value : Q

def slot (inverse : Q → Option Q) (chi : Q) (producer : Bool)
 (s : Slot) (acc : Q) : Option Q :=
 if s.weight.val = 0 then some acc else do
  let inv ← inverse (valueSub chi s.value)
  some (if producer then valueAdd acc (scale inv s.weight)
        else valueSub acc (scale inv s.weight))

def slots (inverse : Q → Option Q) (chi : Q) (producer : Bool) :
 List Slot → Q → Option Q
 | [],acc => some acc
 | s::ss,acc => do
  let next ← slot inverse chi producer s acc
  slots inverse chi producer ss next

theorem slot_canonical (inverse : Q → Option Q) (chi acc out : Q)
 (producer : Bool) (s : Slot) (hc : Canon acc)
 (h : slot inverse chi producer s acc = some out) : Canon out := by
 unfold slot at h
 split at h
 · exact Option.some.inj h ▸ hc
 · cases hi : inverse (valueSub chi s.value) with
   | none => simp only [hi,Option.bind_none] at h; cases h
   | some inv =>
    simp only [hi,Option.bind_some] at h
    have ho : Canon (if producer then valueAdd acc (scale inv s.weight)
        else valueSub acc (scale inv s.weight)) := by
     cases producer
     · exact qm_sub _ _ hc (canonical _ _)
     · exact qm_add _ _ hc (canonical _ _)
    exact Option.some.inj h ▸ ho

theorem slots_canonical (inverse : Q → Option Q) (chi : Q) (producer : Bool)
 (ss : List Slot) (acc out : Q) (hc : Canon acc)
 (h : slots inverse chi producer ss acc = some out) : Canon out := by
 induction ss generalizing acc with
 | nil => exact Option.some.inj h ▸ hc
 | cons s ss ih =>
  simp only [slots] at h
  cases hs : slot inverse chi producer s acc with
  | none => simp only [hs,Option.bind_none] at h; cases h
  | some next =>
   simp only [hs,Option.bind_some] at h
   exact ih next (slot_canonical inverse chi acc next producer s hc hs) h

#print axioms slot_canonical
#print axioms slots_canonical
end R1Z.PV_OWNL_HelperSlots
