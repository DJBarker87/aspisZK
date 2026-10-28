import NBO_Release
import ExtractedMaskQM31Exact
set_option autoImplicit false
noncomputable section
namespace NBO_FieldPorts
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev Q := aspis_core.field.QM31
abbrev NQ := AspisR1SelectedMaskProbe.field.QM31
abbrev NE := NQ × NQ
def toQ (x : Q) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromQ (x : NQ) : Q := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toE (x : Stage2E) : NE := ⟨toQ x.c0,toQ x.c1⟩
def fromE (x : NE) : Stage2E := ⟨fromQ x.1,fromQ x.2⟩
theorem q_roundtrip (x : Q) : fromQ (toQ x)=x := rfl
theorem e_roundtrip (x : Stage2E) : fromE (toE x)=x := rfl
theorem probe_q_roundtrip (x : NQ) : toQ (fromQ x)=x := rfl
theorem probe_e_roundtrip (x : NE) : toE (fromE x)=x := rfl
/-- Literal limb transport into the already proved extracted probe carrier.
No new arithmetic theorem or native multiplication gate is introduced. -/
theorem canonicalQ (x : Q) :
 NBF_PowerStep.Canonical x ↔ ExtractedMaskQM31Exact.CurrentCanonicalQM (toQ x) := by
 constructor
 · intro h
   exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
 · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ k
   fin_cases k <;> assumption
theorem canonicalE (x : Stage2E) :
 NBO_TailDomain.WideCanonical x ↔ (ExtractedMaskQM31Exact.CurrentCanonicalQM (toE x).1 ∧ ExtractedMaskQM31Exact.CurrentCanonicalQM (toE x).2) := by
 exact and_congr (canonicalQ x.c0) (canonicalQ x.c1)
theorem fromQ_canonical (x : NQ) (h : ExtractedMaskQM31Exact.CurrentCanonicalQM x) :
 NBF_PowerStep.Canonical (fromQ x) :=
 (canonicalQ _).mpr (by simpa only [probe_q_roundtrip] using h)
theorem fromE_canonical (x : NE) (h : (ExtractedMaskQM31Exact.CurrentCanonicalQM x.1 ∧ ExtractedMaskQM31Exact.CurrentCanonicalQM x.2)) :
 NBO_TailDomain.WideCanonical (fromE x) :=
 (canonicalE _).mpr (by simpa only [probe_e_roundtrip] using h)
#print axioms q_roundtrip
#print axioms e_roundtrip
#print axioms probe_q_roundtrip
#print axioms probe_e_roundtrip
#print axioms canonicalQ
#print axioms canonicalE
#print axioms fromQ_canonical
#print axioms fromE_canonical
end NBO_FieldPorts
end
