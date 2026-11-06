import NKE_GeometryDomain
set_option autoImplicit false
noncomputable section
namespace NKE_GeometryCuts
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Logical payload of geometry_start/inverse/line. Native allocation identity,
capacity and exact input-array observations remain in the matched certificates.
No full endpoint equality is inserted as an unobserved cut field. -/
structure Cut (before after : verifier.QueryGeometry) : Prop where
 start : after.start=before.start
 inverseSize : after.inverses.val.length=12
 inverseCells : ∀ i,i<12 → after.inverses.val[i]?=before.inverses.val[i]?
 lineSize : after.line_z.val.length=12
 lineCells : ∀ i,i<12 → after.line_z.val[i]?=before.line_z.val[i]?

theorem same (before after : verifier.QueryGeometry)
 (inverseSize : before.inverses.val.length=12) (lineSize : before.line_z.val.length=12)
 (cut : Cut before after) : after=before := by
 have inverses : after.inverses=before.inverses := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases inside : i<12
  · exact cut.inverseCells i inside
  · rw [List.getElem?_eq_none (by rw [cut.inverseSize];omega),
     List.getElem?_eq_none (by rw [inverseSize];omega)]
 have lines : after.line_z=before.line_z := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases inside : i<12
  · exact cut.lineCells i inside
  · rw [List.getElem?_eq_none (by rw [cut.lineSize];omega),
     List.getElem?_eq_none (by rw [lineSize];omega)]
 cases before
 cases after
 cases cut
 simp_all only []

/-- Native returning windows instantiate at the SAME child reply. The domain
is derived here from that child's actual Result, not a new root precondition. -/
theorem at_call (queries : Array U32 22#usize) (reply after : verifier.QueryGeometry)
 (entered : NJC_ClosedCalls.geometry queries 10#usize 22#usize=ok (.Ok reply))
 (cut : Cut reply after) : after=reply := by
 obtain ⟨_,inverseSize,lineSize⟩ := NKE_GeometryDomain.returned queries reply entered
 exact same reply after inverseSize lineSize cut
#print axioms same
#print axioms at_call
end NKE_GeometryCuts
