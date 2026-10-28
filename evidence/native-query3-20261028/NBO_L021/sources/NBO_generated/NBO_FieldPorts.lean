import NBO_Release
import LPh_NativeWide
set_option autoImplicit false
noncomputable section
namespace NBO_FieldPorts
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev Q := aspis_core.field.QM31
abbrev NQ := FIo_FieldBridge.NQ
abbrev NE := FIo_FieldBridge.NE
def toQ (x : Q) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromQ (x : NQ) : Q := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toE (x : Stage2E) : NE := ⟨toQ x.c0,toQ x.c1⟩
def fromE (x : NE) : Stage2E := ⟨fromQ x.c0,fromQ x.c1⟩
theorem q_roundtrip (x : Q) : fromQ (toQ x)=x := rfl
theorem e_roundtrip (x : Stage2E) : fromE (toE x)=x := rfl
theorem native_q_roundtrip (x : NQ) : toQ (fromQ x)=x := rfl
theorem native_e_roundtrip (x : NE) : toE (fromE x)=x := rfl
/-- Literal limb transport into the already proved emitted field carrier.
No new arithmetic theorem or native multiplication gate is introduced. -/
theorem canonicalQ (x : Q) :
 NBF_PowerStep.Canonical x ↔ FIo_QMValues.Canon (toQ x) := by
 constructor
 · intro h
   exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
 · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ k
   fin_cases k <;> assumption
theorem canonicalE (x : Stage2E) :
 NBO_TailDomain.WideCanonical x ↔ FIo_WideValues.Canon (toE x) := by
 exact and_congr (canonicalQ x.c0) (canonicalQ x.c1)
theorem fromQ_canonical (x : NQ) (h : FIo_QMValues.Canon x) :
 NBF_PowerStep.Canonical (fromQ x) :=
 (canonicalQ _).mpr (by simpa only [native_q_roundtrip] using h)
theorem fromE_canonical (x : NE) (h : FIo_WideValues.Canon x) :
 NBO_TailDomain.WideCanonical (fromE x) :=
 (canonicalE _).mpr (by simpa only [native_e_roundtrip] using h)
#print axioms q_roundtrip
#print axioms e_roundtrip
#print axioms native_q_roundtrip
#print axioms native_e_roundtrip
#print axioms canonicalQ
#print axioms canonicalE
#print axioms fromQ_canonical
#print axioms fromE_canonical
end NBO_FieldPorts
end
