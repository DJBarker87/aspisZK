import S9NativeFieldDivisionBoundV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9PartialDotReaderDomainV1
open AspisR1S9NativeFieldS5BoundedReaderV1
open AspisR1S9NativeFieldDivisionBoundV1
open AspisR1S9OwnedFromLimbsMapV1 (mapResult)

def index (s j : Usize) : Usize :=
  Usize.wrapping_add (Usize.wrapping_mul 16#usize s) j

/-- Symbolic bounded source arithmetic: no reduction of the machine modulus. -/
theorem index_exact (s j : Usize) (hs : s.val < 4) (hj : j.val < 16) :
    (index s j).val = 16*s.val+j.val ∧ (index s j).val < 64 := by
  have h64 : (64#usize).val=64 := rfl
  have hsize : 64 < UScalar.size .Usize := by
    simpa only [UScalar.size,h64] using (64#usize).hBounds
  have hm : (Usize.wrapping_mul 16#usize s).val=16*s.val := by
    rw [Usize.wrapping_mul_val_eq]
    change (16*s.val) % UScalar.size .Usize=16*s.val
    exact Nat.mod_eq_of_lt (by omega)
  have hv : (index s j).val=16*s.val+j.val := by
    unfold index
    rw [Usize.wrapping_add_val_eq]
    change ((Usize.wrapping_mul 16#usize s).val+j.val) % UScalar.size .Usize=
      16*s.val+j.val
    rw [hm]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨hv,by rw [hv]; omega⟩

/-- The actual two-fold quotient64 suffices for every source partial-dot
coefficient index. It is not an assertion of exact input byte length. -/
theorem index_maps_s5_reader (bytes : Slice U8) (s j : Usize)
    (hs : s.val < 4) (hj : j.val < 16)
    (hdiv : (Slice.len bytes / 32#usize : Result Usize)=.ok (64#usize)) :
    mapResult toS5 (weights.field bytes (index s j))=
      AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes (index s j) := by
  exact quotient_index_maps_s5_reader bytes 64#usize (index s j) hdiv
    (by simpa using (index_exact s j hs hj).2)

#print axioms index_exact
#print axioms index_maps_s5_reader
end AspisR1S9PartialDotReaderDomainV1
