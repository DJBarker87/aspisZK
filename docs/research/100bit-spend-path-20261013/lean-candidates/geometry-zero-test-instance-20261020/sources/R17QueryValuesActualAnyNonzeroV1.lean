import R17SliceAnySourceV1
import R17QueryValuesCanonical
import R17QueryValuesEntryActualInputBridgeV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace R17QueryValuesActualAnyNonzeroV1
open AspisR1QueryGeometryActual R17QueryValuesWholeBodyStoredV1
open R17QueryValuesWholeBodyV21
open R17QueryValuesEntryActualV1

theorem queryValuesEntry_zeroAny_success_nonzero
    (q : Std.U32) (arr : Array field.M31 5#usize) (z : field.M31)
    (h : emittedRawWithCallees actualSourceCallees
      R17SliceAnySourceV1.queryZeroAny q = .ok (.Ok (arr,z))) :
    (∀ x ∈ arr.val, x ≠ 0#u32) ∧
      ∀ x ∈ arr.val, R17CurrentM31Semantics.decode x ≠ 0 := by
  have hentry : R17QueryValuesEntryActualV1.queryValuesEntry q
      R17SliceAnySourceV1.queryZeroAny = .ok (.Ok (arr,z)) := by
    calc
      R17QueryValuesEntryActualV1.queryValuesEntry q R17SliceAnySourceV1.queryZeroAny =
          directWithCallees actualSourceCallees q R17SliceAnySourceV1.queryZeroAny :=
        (direct_eq_queryValuesEntry q R17SliceAnySourceV1.queryZeroAny).symm
      _ = emittedRawWithCallees actualSourceCallees
          R17SliceAnySourceV1.queryZeroAny q :=
        (emittedRawWithCallees_eq_directWithCallees
          actualSourceCallees q R17SliceAnySourceV1.queryZeroAny).symm
      _ = .ok (.Ok (arr,z)) := h
  obtain ⟨u, ix, iy, point, x, y, _hu, _hix, _hiy, _hixval, _hiyval,
      hcore, harr, ⟨it, it', hrun, hstart, hslice⟩⟩ :=
    R17QueryValuesEntryActualInputBridgeV1.successful_queryValuesEntry_core_with_input
      q R17SliceAnySourceV1.queryZeroAny arr z hentry
  have hlen : it.slice.val.length ≤ Usize.max := it.slice.property
  have hle : it.i ≤ it.slice.val.length := by rw [hstart]; omega
  have hsnd := R17SliceAnySourceV1.queryZeroAny_false_sound
    it.slice.val hlen it rfl hle it' hrun
  have hnonzeroAt (j : Nat) (hj : j < 5) :
      ([point.x,point.y,x,y,z] : List field.M31)[j] ≠ 0#u32 := by
    have hj' : j < it.slice.val.length := by simpa [hslice] using hj
    simpa [hslice, R17SliceAnySourceV1.sourceM31Zero] using
      hsnd.2 j (by rw [hstart]; omega) hj'
  have hn : ∀ a ∈ arr.val, a ≠ 0#u32 := by
    intro a ha
    rw [harr] at ha
    change a ∈ [point.x,point.y,x,y,z] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | ha | ha | ha | ha
    · subst a; exact hnonzeroAt 0 (by decide)
    · subst a; exact hnonzeroAt 1 (by decide)
    · subst a; exact hnonzeroAt 2 (by decide)
    · subst a; exact hnonzeroAt 3 (by decide)
    · subst a; exact hnonzeroAt 4 (by decide)
  constructor
  · exact hn
  · exact R17QueryValuesCanonical.emittedRaw_success_nonzero_decode
      q R17SliceAnySourceV1.queryZeroAny arr z h hn

#print axioms queryValuesEntry_zeroAny_success_nonzero
end R17QueryValuesActualAnyNonzeroV1
