import R1Z.PV_RDB1_V181
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V181Finding
open PV_RDB1_V183_ReserveWorld

/-- Literal empty-byte reference used by the original capacity callback.
The original bounded native credit does not assert unbounded native totality. -/
def bytesReference (_n : Usize) : Result (alloc.vec.Vec U8) :=
  ok (alloc.vec.Vec.new U8)
def decodeEmpty (v : alloc.vec.Vec U8) : Result String :=
  if v.val=[] then ok "" else fail .panic
def originalValue (n : Usize) : Result String := do
  let v ← bytesReference n
  decodeEmpty v

theorem original_always_returns (n : Usize) : originalValue n=ok "" := rfl

/-- Deterministic capacity overflow is a source behaviour, independent of
allocator/OOM assumptions. It occurs before any allocation step. -/
theorem overflow_world {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (hwidth : shape.width=1)
    (address n : Nat) (w : World S F) (over : n>byteMax) :
    (PV_RDB1_V181.deployed step wordMax byteMax shape address n w).returned=
      .error .capacityOverflow ∧
    (PV_RDB1_V181.deployed step wordMax byteMax shape address n w).world=w := by
  unfold PV_RDB1_V181.deployed
  by_cases hw : n>wordMax
  · simp [hw]
  · simp [hw,hwidth,over]

/-- A panic cannot refine an unconditional returned empty String. The
stateful reference law is correct; the total old value callback cannot be
promoted to an unqualified native full-Result law. -/
theorem no_unbounded_promotion (n : Usize) :
    (fail .panic : Result String) ≠ originalValue n := by
  rw [original_always_returns]
  intro h
  cases h

#print axioms original_always_returns
#print axioms overflow_world
#print axioms no_unbounded_promotion
end R1Z.PV_RDB1_V181Finding
