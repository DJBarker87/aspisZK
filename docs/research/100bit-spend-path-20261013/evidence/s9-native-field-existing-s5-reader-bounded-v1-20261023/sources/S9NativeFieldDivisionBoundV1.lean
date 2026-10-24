import S9NativeFieldS5BoundedReaderV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9NativeFieldDivisionBoundV1
open AspisR1S9NativeFieldS5BoundedReaderV1
open AspisR1S9OwnedFromLimbsMapV1 (mapResult)

/-- The SAME successful division used by Pair supplies the byte-window
bound for every index below its actual quotient. No exact byte length or
assumed decoder correctness is required. -/
theorem quotient_index_fits (bytes : Slice U8) (n i : Usize)
    (hdiv : (Slice.len bytes / 32#usize : Result Usize) = .ok n)
    (hi : i.val < n.val) : (i.val + 1) * 32 ≤ bytes.val.length := by
  obtain ⟨q,hq,hqval⟩ := UScalar.div_spec (Slice.len bytes)
    (y := (32#usize)) (by decide)
  have heq : q = n := Result.ok.inj (hq.symm.trans hdiv)
  subst q
  have hlen : (Slice.len bytes).val = bytes.val.length := rfl
  have h32 : (32#usize).val = 32 := rfl
  rw [hlen,h32] at hqval
  omega

/-- Thus the actual Pair quotient bounds are sufficient for the checked
S5 reader bridge, despite the current source using wrapping offsets. -/
theorem quotient_index_maps_s5_reader (bytes : Slice U8) (n i : Usize)
    (hdiv : (Slice.len bytes / 32#usize : Result Usize) = .ok n)
    (hi : i.val < n.val) :
    mapResult toS5 (weights.field bytes i) =
      AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes i := by
  exact native_field_maps_s5_reader bytes i
    (fitting_window_safe bytes i (quotient_index_fits bytes n i hdiv hi))

#print axioms quotient_index_fits
#print axioms quotient_index_maps_s5_reader
end AspisR1S9NativeFieldDivisionBoundV1
