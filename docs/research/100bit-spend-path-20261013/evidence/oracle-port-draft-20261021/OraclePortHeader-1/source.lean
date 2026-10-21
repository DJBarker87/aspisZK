import OraclePortExperiment

/-! Literal compact header admission, matching candidate.rs::parse_shape's
four tests. Relating these stored proof bytes to the erased transcript and
its Public.tag is explicitly separate. -/
set_option autoImplicit false
namespace AspisR1.OraclePortHeader
open AspisV8R19.DuplexFrames

def magic : Bytes := [82,49,80,51,67,66,49,56]
def accepts (proof : Bytes) : Bool := decide (
  proof.length = 57607 ∧ proof.take 8 = magic ∧
  proof[8]? = some 2 ∧ (proof.drop 9).take 7 = List.replicate 7 0)

theorem accepts_iff (proof : Bytes) : accepts proof = true ↔
    proof.length = 57607 ∧ proof.take 8 = magic ∧
    proof[8]? = some 2 ∧ (proof.drop 9).take 7 = List.replicate 7 0 := by
  simp only [accepts, decide_eq_true_eq]

theorem rejects_other_tags (proof : Bytes) (ht : proof[8]? ≠ some 2) :
    accepts proof = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  exact ht ((accepts_iff proof).mp ha).2.2.1

theorem rejects_wrong_length (proof : Bytes) (hl : proof.length ≠ 57607) :
    accepts proof = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  exact hl ((accepts_iff proof).mp ha).1

/-- Header parsing alone imposes no constraint on an unrelated Public tag.
A source adapter must identify the tag carriers; it cannot be inferred. -/
theorem header_does_not_bind_public (proof : Bytes) (tag : Nat)
    (ha : accepts proof = true) : accepts proof = true ∧ tag = tag := ⟨ha,rfl⟩

#print axioms accepts_iff
#print axioms rejects_other_tags
#print axioms rejects_wrong_length
#print axioms header_does_not_bind_public
end AspisR1.OraclePortHeader
