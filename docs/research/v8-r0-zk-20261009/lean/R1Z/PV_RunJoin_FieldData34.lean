import R1Z.ProverRwDictionaryTower
import R1Z.ProverCommitNativeQ48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FieldData34
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
abbrev Q := aspis_core.field.QM31

def old (x : Q) : Old.Q := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def source (x : Old.Q) : Q := ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source x)
def value (x : Q) := decode (old x)
def canonical (x : Q) : Prop := Canonical (old x)

theorem old_source (x : Old.Q) : old (source x) = x := by cases x; rfl
theorem source_old (x : Q) : source (old x) = x := by cases x; rfl

theorem native_source (x : Q) :
    ProverCommitNativeQ48.source (old x) = ProverRwDictionaryTower.toQ x := by cases x; rfl

theorem value_source (x : Old.Q) : value (source x) = decode x := by rw [value,old_source]
theorem canonical_source (x : Old.Q) : canonical (source x) ↔ Canonical x := by rw [canonical,old_source]

variable [ExternalTypes]
/-- Exact full source-result arithmetic at canonical caller values. These
source equations install no native ABI, feature or world-effect law. -/
theorem add (ops : ExternalFuns) (a b : Q) (ha : canonical a) (hb : canonical b) :
    ∃ c, @aspis_core.field.QM31.add _ (ProverRwDictionaryTower.selected ops) a b = .ok c ∧
      canonical c ∧ value c = value a + value b := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.add (old a) (old b) ha hb
  rw [native_source,native_source] at hz
  refine ⟨source z,?_,(canonical_source z).mpr hc,?_⟩
  · change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ _ = _
    rw [hz]
    rfl
  · simpa only [value,old_source] using hd

theorem mul (ops : ExternalFuns) (a b : Q) (ha : canonical a) (hb : canonical b) :
    ∃ c, @aspis_core.field.QM31.mul _ (ProverRwDictionaryTower.selected ops) a b = .ok c ∧
      canonical c ∧ value c = value a * value b := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.mul (old a) (old b) ha hb
  rw [native_source,native_source] at hz
  refine ⟨source z,?_,(canonical_source z).mpr hc,?_⟩
  · change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ _ = _
    rw [hz]
    rfl
  · simpa only [value,old_source] using hd

theorem sub (ops : ExternalFuns) (a b : Q) (ha : canonical a) (hb : canonical b) :
    ∃ c, @aspis_core.field.QM31.sub _ (ProverRwDictionaryTower.selected ops) a b = .ok c ∧
      canonical c ∧ value c = value a - value b := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.sub (old a) (old b) ha hb
  rw [native_source,native_source] at hz
  refine ⟨source z,?_,(canonical_source z).mpr hc,?_⟩
  · change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ _ = _
    rw [hz]
    rfl
  · simpa only [value,old_source] using hd

#print axioms old_source
#print axioms source_old
#print axioms native_source
#print axioms value_source
#print axioms canonical_source
#print axioms add
#print axioms mul
#print axioms sub
end R1Z.PV_RunJoin_FieldData34
