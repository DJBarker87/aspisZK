import AspisR1Qm31SamplerIndex.Funs
import ExtractedCurrentQM31Equality

/-!
Fixed field-copy bridge from the extracted index sampler to the unchanged
current QM31 carrier. The wrapper theorem unfolds the actual generated
qm31_sample body, conditional on actual qm31_digits success. It supplies no
digit-loop, byte-rank, transcript, or Rust-call reachability premise by fiat.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerCarrier

open Aeneas Aeneas.Std Result

abbrev SamplerQM := AspisR1Qm31SamplerIndex.field.QM31
abbrev CurrentQM := AspisR1.ExtractedCurrentQM31Equality.CurrentQM
abbrev CurrentCanonicalQM :=
  AspisR1.ExtractedCurrentQM31Equality.CurrentCanonicalQM
abbrev Digits := Array U32 4#usize

/-- Copy every coordinate, in the source c0.a/c0.b/c1.a/c1.b order. -/
def toCurrent (x : SamplerQM) : CurrentQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def fromCurrent (x : CurrentQM) : SamplerQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

@[simp] theorem fromCurrent_toCurrent (x : SamplerQM) :
    fromCurrent (toCurrent x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

@[simp] theorem toCurrent_fromCurrent (x : CurrentQM) :
    toCurrent (fromCurrent x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem toCurrent_injective : Function.Injective toCurrent := by
  intro x y h
  simpa only [fromCurrent_toCurrent] using congrArg fromCurrent h

theorem toCurrent_coordinates (x : SamplerQM) :
    (toCurrent x).c0.a = x.c0.a ∧ (toCurrent x).c0.b = x.c0.b ∧
    (toCurrent x).c1.a = x.c1.a ∧ (toCurrent x).c1.b = x.c1.b :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A proved-bounded read; no default value is inserted. -/
def digit (ds : Digits) (i : Fin 4) : U32 :=
  ds.val[i.val]'(by have := ds.property; change ds.val.length = 4 at this; omega)

def packed (ds : Digits) : SamplerQM :=
  ⟨⟨digit ds 0, digit ds 1⟩, ⟨digit ds 2, digit ds 3⟩⟩

def DigitsCanonical (ds : Digits) : Prop :=
  ∀ i : Fin 4, (digit ds i).val < 2147483647

private theorem index_four (ds : Digits) (i : Usize) (hi : i.val < 4) :
    Array.index_usize ds i = ok (digit ds ⟨i.val, hi⟩) := by
  have hb : i.val < ds.length := by
    have := ds.property
    change ds.val.length = 4 at this
    change i.val < ds.val.length
    omega
  obtain ⟨x, hx, hval⟩ := WP.spec_imp_exists (Array.index_usize_spec ds i hb)
  simpa only [digit] using hx.trans (congrArg Result.ok hval)

/-- Four actual bounded indices and both actual CM31.new calls are discharged. -/
theorem qm31_sample_of_digits (block : Array U8 32#usize) (ds : Digits)
    (h : AspisR1Qm31SamplerIndex.sampler.qm31_digits block = ok ds) :
    AspisR1Qm31SamplerIndex.sampler.qm31_sample block = ok (packed ds) := by
  have h0 := index_four ds 0#usize (by decide)
  have h1 := index_four ds 1#usize (by decide)
  have h2 := index_four ds 2#usize (by decide)
  have h3 := index_four ds 3#usize (by decide)
  have e0 : (⟨(0#usize).val, by decide⟩ : Fin 4) = 0 := by decide
  have e1 : (⟨(1#usize).val, by decide⟩ : Fin 4) = 1 := by decide
  have e2 : (⟨(2#usize).val, by decide⟩ : Fin 4) = 2 := by decide
  have e3 : (⟨(3#usize).val, by decide⟩ : Fin 4) = 3 := by decide
  simpa only [AspisR1Qm31SamplerIndex.sampler.qm31_sample, h, bind_tc_ok,
    h0, h1, h2, h3, e0, e1, e2, e3,
    AspisR1Qm31SamplerIndex.field.CM31.new, packed]

theorem packed_current_canonical (ds : Digits) (h : DigitsCanonical ds) :
    CurrentCanonicalQM (toCurrent (packed ds)) :=
  ⟨⟨h 0, h 1⟩, ⟨h 2, h 3⟩⟩

theorem packed_current_coordinates (ds : Digits) :
    AspisR1.ExtractedCurrentTowerAdd.wordsQM (toCurrent (packed ds)) =
      (((digit ds 0).val, (digit ds 1).val),
       ((digit ds 2).val, (digit ds 3).val)) := rfl

/-- Compose an actual digits result with this fixed carrier map. -/
theorem qm31_sample_current (block : Array U8 32#usize) (ds : Digits)
    (h : AspisR1Qm31SamplerIndex.sampler.qm31_digits block = ok ds)
    (hc : DigitsCanonical ds) :
    ∃ q : SamplerQM,
      AspisR1Qm31SamplerIndex.sampler.qm31_sample block = ok q ∧
      toCurrent q = toCurrent (packed ds) ∧ CurrentCanonicalQM (toCurrent q) :=
  ⟨packed ds, qm31_sample_of_digits block ds h, rfl,
    packed_current_canonical ds hc⟩

/-- Reuse the current exact-tower equality theorem, with canonicality explicit. -/
theorem decode_toCurrent_eq_iff (x y : SamplerQM)
    (hx : CurrentCanonicalQM (toCurrent x))
    (hy : CurrentCanonicalQM (toCurrent y)) :
    AspisR1.ExtractedCurrentQM31Exact.decode (toCurrent x) =
      AspisR1.ExtractedCurrentQM31Exact.decode (toCurrent y) ↔ x = y := by
  rw [AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff _ _ hx hy]
  exact toCurrent_injective.eq_iff

#print axioms fromCurrent_toCurrent
#print axioms toCurrent_fromCurrent
#print axioms toCurrent_injective
#print axioms toCurrent_coordinates
#print axioms qm31_sample_of_digits
#print axioms packed_current_canonical
#print axioms packed_current_coordinates
#print axioms qm31_sample_current
#print axioms decode_toCurrent_eq_iff

end AspisR1.ExtractedQM31SamplerCarrier
