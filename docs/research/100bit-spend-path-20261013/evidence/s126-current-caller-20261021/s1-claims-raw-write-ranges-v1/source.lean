import Aeneas
set_option autoImplicit false
namespace AspisS1ClaimsRawWriteRanges

/-- Byte offsets relative to the allocated Claims object. The 464/16/4
layout is checked by the native leaf harness for its pinned target. This
predicate models write coverage, not an asserted native heap interpretation. -/
def RowBytes (p byte : Nat) : Prop := p*464 ≤ byte ∧ byte < (p+1)*464

def written (initial : Nat → Prop) : Nat → Nat → Prop
  | 0 => initial
  | n+1 => fun byte => written initial n byte ∨ RowBytes n byte

/-- Induction over the number of completed actual-sized row writes. There is
no initialized-storage premise: the initial byte predicate is arbitrary. -/
theorem prefix_covered (initial : Nat → Prop) (n : Nat) :
    ∀ byte, byte < n*464 → written initial n byte := by
  induction n with
  | zero => intro byte bound; omega
  | succ n ih =>
    intro byte bound
    by_cases old : byte < n*464
    · exact Or.inl (ih byte old)
    · exact Or.inr ⟨by omega,by omega⟩

/-- The modeled stores do not change initializedness outside their prefix.
Actual native frame/ownership transport is a separate obligation. -/
theorem outside_frame (initial : Nat → Prop) (n byte : Nat) (outside : n*464 ≤ byte) :
    written initial n byte ↔ initial byte := by
  induction n with
  | zero => rfl
  | succ n ih =>
    constructor
    · intro h
      cases h with
      | inl old => exact (ih (by omega)).mp old
      | inr fresh => unfold RowBytes at fresh; omega
    · intro h
      exact Or.inl ((ih (by omega)).mpr h)

theorem three_rows_covered (initial : Nat → Prop) :
    ∀ byte, byte < 1392 → written initial 3 byte := by
  exact prefix_covered initial 3

/-- Every payload byte belongs to exactly one row, one QM31, one native word
and one byte of that word. No large array or concrete memory is normalized. -/
theorem byte_partition (byte : Nat) (bound : byte < 1392) :
    ∃ p i word lane : Nat, p < 3 ∧ i < 29 ∧ word < 4 ∧ lane < 4 ∧
      byte = p*464+i*16+word*4+lane := by
  refine ⟨byte/464,(byte%464)/16,((byte%464)%16)/4,((byte%464)%16)%4,?_⟩
  omega

/-- Exact flattened source domains. In particular the decoder's p*29 offsets
and last claimed scalar index cannot overflow even a 32-bit usize. -/
theorem source_offsets (p i word lane : Nat)
    (hp : p < 3) (hi : i < 29) (hw : word < 4) (hl : lane < 4) :
    p*29 ≤ 58 ∧ p*29+i < 87 ∧ p*464 ≤ 928 ∧
    p*464+i*16+word*4+lane < 1392 ∧
    p*464+i*16+word*4+lane < 2147483647 ∧
    p*29+i < 4294967295 := by omega

theorem rows_disjoint (p q byte : Nat) (before : p < q)
    (left : RowBytes p byte) : ¬ RowBytes q byte := by
  unfold RowBytes at *
  omega

theorem unique_coordinates (p i w b q j v c : Nat)
    (hp : p < 3) (hi : i < 29) (hw : w < 4) (hb : b < 4)
    (hq : q < 3) (hj : j < 29) (hv : v < 4) (hc : c < 4)
    (same : p*464+i*16+w*4+b = q*464+j*16+v*4+c) :
    p=q ∧ i=j ∧ w=v ∧ b=c := by omega

#print axioms prefix_covered
#print axioms outside_frame
#print axioms three_rows_covered
#print axioms byte_partition
#print axioms source_offsets
#print axioms rows_disjoint
#print axioms unique_coordinates
end AspisS1ClaimsRawWriteRanges
