import PV_STX2_Source7EntryOwnedIndexed
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7ColumnView
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_STX2_Source7EntryOwned
/-- Conditional on owner acceptance of the translator patch. A proof view
whose first column is i. This only transports the closed return theorem's
input; it is not a claim about the emitted loop's current control state. -/
def focus (value : Foundation) (i : Fin value.c1.val.length) : Foundation :=
  ⟨⟨List.ofFn (fun _ : Fin 16 => value.c1.val[i]), by simp⟩⟩
/-- Conditional on owner acceptance of the translator patch. Every column in
the focused proof view has exactly column i's values, without codec evaluation. -/
theorem values_focus (value : Foundation) (i : Fin value.c1.val.length)
    (j : Fin (focus value i).c1.val.length) :
    values (focus value i) j = values value i := by
  change (List.ofFn (fun _ : Fin 16 => value.c1.val[i]))[j.val].val = _
  rw [List.getElem_ofFn]
  rfl
/-- Conditional on owner acceptance of the translator patch. Transport only
the existing entry ownership obligation; no new OWNER place is selected from
an endpoint or by a search for matching erased values. -/
theorem owned {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value)
    (i : Fin value.c1.val.length) : Source7EntryOwned s (focus value i) := by
  intro j
  simpa only [values_focus value i j] using entry i
/-- Conditional on owner acceptance of the translator patch. Equality of the
entry existential propositions transports the choice, not an erased-value
search in an executed store. -/
theorem place {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value)
    (i : Fin value.c1.val.length) (j : Fin (focus value i).c1.val.length) :
    PV_STX2_Source7EntrySelection.place (owned entry i) j =
    PV_STX2_Source7EntrySelection.place entry i := by
  unfold PV_STX2_Source7EntrySelection.place
  congr 1
  simp only [values_focus value i j]
/-- Conditional on owner acceptance of the translator patch. The focused
view retains the exact entry identity of column i. -/
theorem identity {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value)
    (i : Fin value.c1.val.length) (j : Fin (focus value i).c1.val.length) :
    PV_STX2_Source7EntrySelection.identity (owned entry i) j =
    PV_STX2_Source7EntrySelection.identity entry i := by
  unfold PV_STX2_Source7EntrySelection.identity
  congr 1
  simp only [values_focus value i j]
/-- Conditional on owner acceptance of the translator patch. The focused
view retains the complete source header of column i. -/
theorem header {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value)
    (i : Fin value.c1.val.length) (j : Fin (focus value i).c1.val.length) :
    PV_STX2_Source7EntrySelection.header (owned entry i) j =
    PV_STX2_Source7EntrySelection.header entry i := by
  unfold PV_STX2_Source7EntrySelection.header
  congr 1
  simp only [values_focus value i j]
#print axioms focus
#print axioms values_focus
#print axioms owned
#print axioms place
#print axioms identity
#print axioms header
end PV_STX2_Source7ColumnView
