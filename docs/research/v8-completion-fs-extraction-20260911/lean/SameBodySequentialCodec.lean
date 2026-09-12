import SameBodyChunkParser

/-! Literal sequential canonical-limb decoder versus the existing combined
guard. Rust ordering is c0.a, c0.b, c1.a, c1.b; a failed M31 decode returns
before later decodes. This is a field/byte-level source-shaped model, not an
Aeneas translation of Rust `from_le_bytes` or iterator execution semantics.
Only four small branch conditions are split, never the QM31 field/domain.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
namespace AspisV8.SameBodySequentialCodec
open AspisV5ComponentCQM31Representation AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler
noncomputable section

def sequentialLimbs (bytes : QM31Bytes) : Option QM31Limbs := do
  let a ← decodeM31LE (qm31LimbBytes bytes 0)
  let b ← decodeM31LE (qm31LimbBytes bytes 1)
  let c ← decodeM31LE (qm31LimbBytes bytes 2)
  let d ← decodeM31LE (qm31LimbBytes bytes 3)
  pure ![a,b,c,d]

theorem forall_four (P : Fin 4 → Prop) :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0,h 1,h 2,h 3⟩
  · intro h i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

theorem sequentialLimbs_eq (bytes : QM31Bytes) :
    sequentialLimbs bytes = decodeQM31LE bytes := by
  by_cases h0 : (decodeWordLE (qm31LimbBytes bytes 0)).val < m31Modulus
  <;> by_cases h1 : (decodeWordLE (qm31LimbBytes bytes 1)).val < m31Modulus
  <;> by_cases h2 : (decodeWordLE (qm31LimbBytes bytes 2)).val < m31Modulus
  <;> by_cases h3 : (decodeWordLE (qm31LimbBytes bytes 3)).val < m31Modulus
  <;> simp [sequentialLimbs, decodeM31LE, decodeQM31LE, forall_four, h0,h1,h2,h3]
  all_goals
    funext i
    fin_cases i <;> rfl

def sequentialExact (bytes : QM31Bytes) : Option QM31Exact :=
  (sequentialLimbs bytes).map qm31ExactLimbEquiv

theorem sequentialExact_eq (bytes : QM31Bytes) :
    sequentialExact bytes = decodeQM31ExactLE bytes := by
  unfold sequentialExact decodeQM31ExactLE
  rw [sequentialLimbs_eq]

/-- The first failing limb always rejects; there is no unchecked fallback
value and no requirement to inspect the remaining limbs after failure. -/
theorem high_limb_rejects (bytes : QM31Bytes) (limb : Fin 4)
    (high : m31Modulus ≤ (decodeWordLE (qm31LimbBytes bytes limb)).val) :
    sequentialExact bytes = none := by
  rw [sequentialExact_eq]
  exact CanonicalRelationInput.noncanonical_field bytes limb high

def cursor (body : List Byte) (offset : Nat) : Nat → Option (List QM31Exact)
  | 0 => some []
  | n+1 => do
    let value ← sequentialExact (SameBodyChunkParser.chunk body offset)
    let rest ← cursor body (offset+16) n
    pure (value::rest)

theorem cursor_eq (body : List Byte) (n offset : Nat) :
    cursor body offset n = SameBodyChunkParser.cursor body offset n := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    simp only [cursor, SameBodyChunkParser.cursor, sequentialExact_eq, ih]

/-- The independently defined guarded loop now uses the literal sequential
limb-decoder model rather than taking the combined decoder as its primitive. -/
def fields (body : List Byte) : Option (List QM31Exact) :=
  if SameBodyChunkParser.sourceBadLength body.length then none else cursor body 0 697

theorem fields_eq_parseFixed (body : List Byte) :
    fields body = CanonicalRelationInput.parseFixed body := by
  unfold fields
  rw [cursor_eq]
  exact SameBodyChunkParser.fields_eq_parseFixed body

#print fields_eq_parseFixed
#print axioms sequentialLimbs_eq
#print axioms sequentialExact_eq
#print axioms high_limb_rejects
#print axioms cursor_eq
#print axioms fields_eq_parseFixed
end
end AspisV8.SameBodySequentialCodec
