import AspisV8R19.R472CheckedConstructor

/-! A 64-bit word runtime refining the explicit allocation fragment. Address
arithmetic is actual BitVec arithmetic; origin is retained independently.
This is not a Rust/LLBC pointer-semantics or caller-validity theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R475PointerWordRuntime
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R433ConstructorFragment

structure WordPointer where
  address : BitVec 64
  origin : Option (Nat × Nat)

def decodePointer (ptr : WordPointer) : Pointer :=
  ⟨ptr.address.toNat, ptr.origin⟩

structure WordIter where
  first : WordPointer
  last : WordPointer

inductive WordValue where
  | sliceRef (pointer : WordPointer) (length : BitVec 64)
  | rawFat (mutability : Mutability) (pointer : WordPointer) (length : BitVec 64)
  | nonNullFat (pointer : WordPointer) (length : BitVec 64)
  | rawThin (mutability : Mutability) (pointer : WordPointer)
  | nonNullThin (pointer : WordPointer)
  | word (value : BitVec 64)
  | marker
  | iterator (value : WordIter)

def decode : WordValue → Value
  | .sliceRef ptr len => .sliceRef (decodePointer ptr) len.toNat
  | .rawFat mutability ptr len => .rawFat mutability (decodePointer ptr) len.toNat
  | .nonNullFat ptr len => .nonNullFat (decodePointer ptr) len.toNat
  | .rawThin mutability ptr => .rawThin mutability (decodePointer ptr)
  | .nonNullThin ptr => .nonNullThin (decodePointer ptr)
  | .word value => .word value.toNat
  | .marker => .marker
  | .iterator value => .iterator ⟨decodePointer value.first, decodePointer value.last⟩

def rawCast : Cast → WordValue → Option WordValue
  | .sharedFatToNonNullFat, .rawFat .shared ptr len => some (.nonNullFat ptr len)
  | .nonNullFatToMutFat, .nonNullFat ptr len => some (.rawFat .mut ptr len)
  | .mutFatToMutThin, .rawFat .mut ptr _ => some (.rawThin .mut ptr)
  | .mutThinToNonNullThin, .rawThin .mut ptr => some (.nonNullThin ptr)
  | .nonNullThinToMutThin, .nonNullThin ptr => some (.rawThin .mut ptr)
  | .mutThinToSharedThin, .rawThin .mut ptr => some (.rawThin .shared ptr)
  | .wordToSharedThin, .word len => some (.rawThin .shared ⟨len, none⟩)
  | _, _ => none

def validCastResult : WordValue → Bool
  | .nonNullFat ptr _ => decide (ptr.address ≠ BitVec.ofNat 64 0)
  | .nonNullThin ptr => decide (ptr.address ≠ BitVec.ofNat 64 0)
  | _ => true

def checkedCast (kind : Cast) (value : WordValue) : Option WordValue := do
  let result ← rawCast kind value
  if validCastResult result then some result else none

theorem zero_guard (address : BitVec 64) :
    decide (address ≠ BitVec.ofNat 64 0) = decide (0 < address.toNat) := by
  by_cases hz : address = BitVec.ofNat 64 0
  · simp [hz]
  · have hp : 0 < address.toNat := by
      by_contra h
      have hv : address.toNat = 0 := by omega
      apply hz
      apply BitVec.eq_of_toNat_eq
      simpa using hv
    simp [hz, hp]

theorem raw_cast_decode (kind : Cast) (value : WordValue) :
    (rawCast kind value).map decode = castValue kind (decode value) := by
  cases kind <;> cases value <;> try rfl
  all_goals cases ‹Mutability› <;> rfl

theorem valid_cast_decode (value : WordValue) :
    validCastResult value = R472CheckedConstructor.validCastResult (decode value) := by
  cases value <;> simp only [validCastResult, decode,
    R472CheckedConstructor.validCastResult, decodePointer]
  all_goals first | rfl | exact zero_guard _

theorem checked_cast_decode (kind : Cast) (value : WordValue) :
    (checkedCast kind value).map decode =
      R472CheckedConstructor.checkedCast kind (decode value) := by
  have hc := raw_cast_decode kind value
  cases h : rawCast kind value with
  | none =>
      simp [h] at hc
      simp [checkedCast, h, R472CheckedConstructor.checkedCast, ← hc]
  | some result =>
      simp [h] at hc
      by_cases hg : validCastResult result = true
      · simp [checkedCast, h, R472CheckedConstructor.checkedCast,
          ← hc, ← valid_cast_decode, hg]
      · simp [checkedCast, h, R472CheckedConstructor.checkedCast,
          ← hc, ← valid_cast_decode, hg]

theorem mul16_no_wrap (count : BitVec 64)
    (h : count.toNat * 16 < 2 ^ 64) :
    (count * BitVec.ofNat 64 16).toNat = count.toNat * 16 := by
  have h16 : (BitVec.ofNat 64 16).toNat = 16 := rfl
  rw [BitVec.toNat_mul, h16, Nat.mod_eq_of_lt h]

theorem add_no_wrap (left right : BitVec 64)
    (h : left.toNat + right.toNat < 2 ^ 64) :
    (left + right).toNat = left.toNat + right.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

def offset {T : Type} (heap : Heap T) (ptr : WordPointer)
    (count : BitVec 64) : Option WordPointer :=
  if count.toNat = 0 then some ptr else do
    let (id, position) ← ptr.origin
    let a ← heap id
    if ptr.address.toNat = a.base + position ∧
        position + count.toNat * 16 ≤ a.cells.length * 16 then
      some ⟨ptr.address + count * BitVec.ofNat 64 16,
        some (id, position + count.toNat * 16)⟩
    else none

theorem offset_decode {T : Type} (heap : Heap T) (ptr : WordPointer)
    (count : BitVec 64) :
    (offset heap ptr count).map decodePointer =
      add heap (decodePointer ptr) count.toNat := by
  by_cases hz : count.toNat = 0
  · simp [offset, add, hz]
  · cases ho : ptr.origin with
    | none => simp [offset, add, decodePointer, hz, ho]
    | some origin =>
      rcases origin with ⟨id, position⟩
      cases ha : heap id with
      | none => simp [offset, add, decodePointer, hz, ho, ha]
      | some a =>
        by_cases hc : ptr.address.toNat = a.base + position ∧
            position + count.toNat * 16 ≤ a.cells.length * 16
        · have hn := a.noWrap
          have hb : ptr.address.toNat + count.toNat * 16 < 2 ^ 64 := by omega
          have hm : count.toNat * 16 < 2 ^ 64 := by omega
          have hmul := mul16_no_wrap count hm
          have hadd := add_no_wrap ptr.address (count * BitVec.ofNat 64 16)
            (by rw [hmul]; exact hb)
          rw [hmul] at hadd
          simp [offset, add, decodePointer, hz, ho, ha, hc, hadd]
        · simp [offset, add, decodePointer, hz, ho, ha, hc]

#print axioms decodePointer
#print axioms decode
#print axioms rawCast
#print axioms validCastResult
#print axioms checkedCast
#print axioms zero_guard
#print axioms raw_cast_decode
#print axioms valid_cast_decode
#print axioms checked_cast_decode
#print axioms mul16_no_wrap
#print axioms add_no_wrap
#print axioms offset
#print axioms offset_decode
end AspisV8R19.R475PointerWordRuntime
