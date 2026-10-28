-- Retargeted inherited proof body; only module imports changed.
import NCD_B_NBQ_Powers29
import RPt_FIo_ArrayCanon
set_option autoImplicit false
namespace NBS_PowersCanon
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
/-- The coefficient domain for every term and tail is derived from the SAME
29-power call on the SAME gamma, not supplied for a separately chosen array. -/
theorem source (gamma : NE) (hg : canonE gamma) :
    ∃ g, FIo_Native.weights.powers 29#usize gamma=ok g ∧ FIo_ArrayCanon.Holds g := by
  obtain ⟨g,run,holds⟩ := NBQ_Powers29.source gamma hg
  refine ⟨g,run,?_⟩
  intro x hx
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hx
  have bound : i<29 := by
    have len : g.val.length=29 := g.property
    omega
  obtain ⟨z,get,canonical,_⟩ := holds i bound
  rw [List.getElem?_eq_getElem hi] at get
  have same : z=x := (Option.some.inj get).symm.trans eq
  exact same ▸ canonical
#print axioms source
end NBS_PowersCanon
