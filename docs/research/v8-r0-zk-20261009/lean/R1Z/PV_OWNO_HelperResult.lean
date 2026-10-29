import R1Z.PV_OWNL_HelperSlots
set_option autoImplicit false
namespace R1Z.PV_OWNO_HelperResult
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNL_Scale PV_OWNL_HelperSlots
attribute [local irreducible] PV_B2_FieldValue.aspis_core.field.QM31.add
 PV_B2_FieldValue.aspis_core.field.QM31.sub

/-- Source row view; fixed two-element array association remains separate. -/
structure Row where
 producers : List Slot
 consumers : List Slot

/-- The two active-pole fields retained by the deployed LogUp error. -/
structure Pole where
 row : Nat
 producer : Bool
 deriving DecidableEq

def slotResult (inverse : Q → Option Q) (chi : Q) (row : Nat)
 (producer : Bool) (s : Slot) (acc : Q) : Except Pole Q :=
 if s.weight.val = 0 then .ok acc else
 match inverse (valueSub chi s.value) with
 | none => .error ⟨row,producer⟩
 | some inv => .ok (if producer then valueAdd acc (scale inv s.weight)
   else valueSub acc (scale inv s.weight))

def slotsResult (inverse : Q → Option Q) (chi : Q) (row : Nat) (producer : Bool) :
 List Slot → Q → Except Pole Q
 | [],acc => .ok acc
 | s::ss,acc => match slotResult inverse chi row producer s acc with
   | .error e => .error e
   | .ok next => slotsResult inverse chi row producer ss next

def rowResult (inverse : Q → Option Q) (chi : Q) (index : Nat) (r : Row) : Except Pole Q :=
 match slotsResult inverse chi index true r.producers zero with
 | .error e => .error e
 | .ok p => slotsResult inverse chi index false r.consumers p

def vectorResult (inverse : Q → Option Q) (chi : Q) :
 Nat → List Row → Except Pole (List Q)
 | _,[] => .ok []
 | index,r::rs => match rowResult inverse chi index r with
   | .error e => .error e
   | .ok value => match vectorResult inverse chi (index+1) rs with
     | .error e => .error e
     | .ok rest => .ok (value::rest)

/-- Forgetting errors is used only to consume the existing success invariant. -/
def erase {E A : Type} : Except E A → Option A
 | .error _ => none
 | .ok x => some x

theorem slot_erasure (inverse : Q → Option Q) (chi : Q) (index : Nat)
 (producer : Bool) (s : Slot) (acc : Q) :
 erase (slotResult inverse chi index producer s acc) = slot inverse chi producer s acc := by
 by_cases hz : s.weight.val = 0
 · simp only [slotResult,slot,if_pos hz,erase]
 · simp only [slotResult,slot,if_neg hz]
   cases inverse (valueSub chi s.value) <;> rfl

theorem slots_erasure (inverse : Q → Option Q) (chi : Q) (index : Nat)
 (producer : Bool) (ss : List Slot) (acc : Q) :
 erase (slotsResult inverse chi index producer ss acc) = slots inverse chi producer ss acc := by
 induction ss generalizing acc with
 | nil => rfl
 | cons s ss ih =>
  have h := slot_erasure inverse chi index producer s acc
  cases hs : slotResult inverse chi index producer s acc with
  | error e =>
   have hz : slot inverse chi producer s acc = none := by simpa only [hs,erase] using h.symm
   simp only [slotsResult,hs,erase,slots,hz]
   rfl
  | ok next =>
   have hz : slot inverse chi producer s acc = some next := by simpa only [hs,erase] using h.symm
   simp only [slotsResult,hs,slots,hz]
   change erase (slotsResult inverse chi index producer ss next) =
    slots inverse chi producer ss next
   exact ih next

theorem successful_slots (inverse : Q → Option Q) (chi : Q)
 (index : Nat) (producer : Bool) (ss : List Slot) (acc out : Q)
 (hc : Canon acc) (h : slotsResult inverse chi index producer ss acc = .ok out) :
 Canon out := by
 have he := slots_erasure inverse chi index producer ss acc
 rw [h] at he
 exact slots_canonical inverse chi producer ss acc out hc he.symm

theorem successful_row (inverse : Q → Option Q) (chi : Q)
 (index : Nat) (r : Row) (out : Q) (h : rowResult inverse chi index r = .ok out) :
 Canon out := by
 cases hs : slotsResult inverse chi index true r.producers zero with
 | error e => simp only [rowResult,hs] at h; cases h
 | ok p =>
  have hc := successful_slots inverse chi index true r.producers zero p zero_canon hs
  have hout : slotsResult inverse chi index false r.consumers p = .ok out := by
   simpa only [rowResult,hs] using h
  exact successful_slots inverse chi index false r.consumers p out hc hout

theorem successful_canonical (inverse : Q → Option Q) (chi : Q)
 (index : Nat) (rs : List Row) (out : List Q)
 (h : vectorResult inverse chi index rs = .ok out) : ∀ q ∈ out, Canon q := by
 induction rs generalizing index out with
 | nil =>
  have he : ([] : List Q) = out := Except.ok.inj h
  cases he
  intro q hq
  cases hq
 | cons r rs ih =>
  cases hr : rowResult inverse chi index r with
  | error e => simp only [vectorResult,hr] at h; cases h
  | ok value =>
   cases hv : vectorResult inverse chi (index+1) rs with
   | error e => simp only [vectorResult,hr,hv] at h; cases h
   | ok rest =>
    have hok : (Except.ok (value::rest) : Except Pole (List Q)) = .ok out := by
     simpa only [vectorResult,hr,hv] using h
    cases Except.ok.inj hok
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact successful_row inverse chi index r q hr
    · exact ih (index+1) rest hv q hq

/-- Source outer helper preserves upstream errors and maps every pole to the
existing CopyImbalance tag; it does not assume success of the row builder. -/
def selectedHelper {E : Type} (imbalance : E) (inverse : Q → Option Q) (chi : Q)
 (rows : Except E (List Row)) : Except E (List Q) :=
 match rows with
 | .error e => .error e
 | .ok rs => match vectorResult inverse chi 0 rs with
   | .error _ => .error imbalance
   | .ok out => .ok out

theorem selected_success_canonical {E : Type} (imbalance : E)
 (inverse : Q → Option Q) (chi : Q) (rows : Except E (List Row)) (out : List Q)
 (h : selectedHelper imbalance inverse chi rows = .ok out) : ∀ q ∈ out, Canon q := by
 cases rows with
 | error e => cases h
 | ok rs =>
  cases hv : vectorResult inverse chi 0 rs with
  | error e => simp only [selectedHelper,hv] at h; cases h
  | ok values =>
   have hok : (Except.ok values : Except E (List Q)) = .ok out := by
    simpa only [selectedHelper,hv] using h
   have he : values = out := Except.ok.inj hok
   exact he ▸ successful_canonical inverse chi 0 rs values hv

#print axioms slot_erasure
#print axioms slots_erasure
#print axioms successful_slots
#print axioms successful_row
#print axioms successful_canonical
#print axioms selected_success_canonical
end R1Z.PV_OWNO_HelperResult
