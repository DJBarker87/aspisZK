import R1Z.PV_CB_CanonicalM31
import R1Z.PV_CB_CurrentQuartic
import R1Z.ProverCommitNativeQ48
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalTower
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
abbrev C := aspis_core.field.CM31
abbrev OldQ := ProverCommitPrimitive47.Old.Q

def old (q : Q) : OldQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def current (q : OldQ) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def Valid (q : Q) : Prop := AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM (old q)

theorem roundtrip (q : Q) : current (old q) = q := by
  cases q; rfl

theorem old_roundtrip (q : OldQ) : old (current q) = q := by
  cases q; rfl

theorem source (q : Q) : ProverRwDictionaryTower.toQ q =
    ProverCommitNativeQ48.source (old q) := rfl

theorem source_current (q : OldQ) :
    ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source q) = current q := rfl

theorem valid_current (q : OldQ)
    (valid : AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM q) : Valid (current q) := by
  simpa only [Valid,old_roundtrip] using valid
#print axioms roundtrip
#print axioms old_roundtrip
#print axioms source
#print axioms source_current
#print axioms valid_current
end R1Z.PV_CB_CanonicalTower
