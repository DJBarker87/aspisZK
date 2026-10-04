
import AspisR515SharedGamma.QmCrossRange
import AspisV8R19.R161WrappedMulExecution
import AspisV8R19.R164ProductExecution
import AspisV8R19.R489WordArithmetic
import AspisV8R19.PartialProduct
import AspisR614SelectedCombineBeta.Funs

/-!
UNVERIFIED proof draft for the actual captured R614 `r83_mixed_limb`.

This is an unverified source-proof draft for the corrected generated R614
Funs module. It introduces only mathematical
definitions and arithmetic lemmas; it contains no axioms, `sorry`, or assumed
source-execution statements.

The eventual source theorem has exactly these inputs and assumptions:
  * source `L` and `slot`, with `L.val < 4` and `slot.val < 4`;
  * all 26 c1 words, all 48 c2 words, and all 26x4 c1-limb / 12x4 mixed
    coefficient words have value `< P`.

Its conclusion is that the captured
`AspisR614SelectedCombineBeta.query_arithmetic.r83_mixed_limb`
returns `.ok z`, with `z.val < P` and `z.val` equal modulo `P` to the
26-term c1 dot product plus the 12 c2/mixed terms indexed by
`16*(j/4)+4*slot.val+j%4`. See
`.r21-scratch/r614-scalar-constants/R83_MIXED_LIMB_PROOF_PLAN.md` for the
fully written statement and staged source proof route.

The following is the exact intended proposition shape, expressed as a comment
so this uncompiled preparation file does not leave a theorem with an unproved
body. `arrayAt` below is the only accessor needed to make its sums explicit:

```lean
∀ (L slot : Usize) (c1 : Array U32 26#usize)
    (c2 : Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients),
  L.val < 4 → slot.val < 4 →
  (∀ i : Fin 26, (arrayAt c1 i).val < P) →
  (∀ i : Fin 48, (arrayAt c2 i).val < P) →
  (∀ i : Fin 26, ∀ r : Fin 4,
    (arrayAt (arrayAt p.c1_limbs i) r).val < P) →
  (∀ i : Fin 12, ∀ r : Fin 4,
    (arrayAt (arrayAt p.mixed i) r).val < P) →
  ∃ z : AspisR614SelectedCombineBeta.aspis_core.field.M31,
    AspisR614SelectedCombineBeta.query_arithmetic.r83_mixed_limb
      L c1 c2 slot p = .ok z ∧ z.val < P ∧
    z.val =
      ((∑ i : Fin 26,
          (arrayAt c1 i).val *
            (arrayAt (arrayAt p.c1_limbs i) ⟨L.val, by omega⟩).val) +
       (∑ j : Fin 12,
          (arrayAt c2 ⟨16*(j.val/4)+4*slot.val+j.val%4, by omega⟩).val *
          (arrayAt (arrayAt p.mixed j) ⟨L.val, by omega⟩).val)) % P
```
```
-/


set_option autoImplicit false

namespace AspisV8R19.R616MixedLimbExecution

open Aeneas Aeneas.Std Result
open AspisV8R19.R159WideBaseExecution AspisV8R19.InverseRuntimeMul
open scoped BigOperators

private abbrev P : Nat := AspisV8.QmCross.p

/-- Read a dependent Aeneas array at a proof-carrying natural index. -/
private def arrayAt {α : Type} {n : Usize} (a : Aeneas.Std.Array α n)
    (i : Fin n.val) : α :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

/-- Exact success behavior of the source's checked array-index operation under
the corresponding length bound. The failure branch remains in the operation;
this lemma discharges it only where the actual source index is in range. -/
private theorem selected_index_ok {α : Type} {n : Usize}
    (a : Aeneas.Std.Array α n) (i : Usize) (hi : i.val < n.val) :
    Aeneas.Std.Array.index_usize a i =
      .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Aeneas.Std.Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) =
      Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private def selected_mixed_index (j slot : Usize) : Result Usize := do
  let q ← j / 4#usize
  let i ← lift (Std.Usize.wrapping_mul 16#usize q)
  let s ← lift (Std.Usize.wrapping_mul 4#usize slot)
  let a ← lift (Std.Usize.wrapping_add i s)
  let r ← j % 4#usize
  lift (Std.Usize.wrapping_add a r)

/-- The captured checked division/remainder and wrapped index arithmetic for
each mixed coefficient succeeds with the exact public c2 index. -/
theorem selected_mixed_index_spec (j slot : Usize)
    (hj : j.val < 12) (hslot : slot.val < 4) :
    ∃ index : Usize, selected_mixed_index j slot = .ok index ∧
      index.val = 16 * (j.val / 4) + 4 * slot.val + j.val % 4 := by
  obtain ⟨q, hq, hqv⟩ := AspisV8R19.R489WordArithmetic.div_four j
  obtain ⟨r, hr, hrv⟩ := AspisV8R19.R489WordArithmetic.rem_four j
  have hdiv : (j / 4#usize : Result Usize) = .ok q := by
    simpa [HDiv.hDiv] using hq
  have hrem : (j % 4#usize : Result Usize) = .ok r := by
    simpa [HMod.hMod] using hr
  rw [selected_mixed_index, hdiv, hrem]
  simp only [bind_tc_ok, lift]
  refine ⟨Std.Usize.wrapping_add
    (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 16#usize q)
      (Std.Usize.wrapping_mul 4#usize slot)) r, rfl, ?_⟩
  rw [Std.Usize.wrapping_add_val_eq, Std.Usize.wrapping_add_val_eq,
    Std.Usize.wrapping_mul_val_eq, Std.Usize.wrapping_mul_val_eq,
    hqv, hrv]
  simp only [UScalar.size]
  have hm16 : 16 * (j.val / 4) < UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    scalar_tac
  have hm4 : 4 * slot.val < UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    scalar_tac
  have ha : 16 * (j.val / 4) + 4 * slot.val < UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    scalar_tac
  have hall : 16 * (j.val / 4) + 4 * slot.val + j.val % 4 <
      UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    scalar_tac
  rw [Nat.mod_eq_of_lt hm16, Nat.mod_eq_of_lt hm4, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hall]
  omega

/-- A four-product canonical M31 chunk fits in one U64 word. -/
theorem fourProducts_lt_u64 (a b c d e f g h : Nat)
    (ha : a < P) (hb : b < P) (hc : c < P) (hd : d < P)
    (he : e < P) (hf : f < P) (hg : g < P) (hh : h < P) :
    a*b + c*d + e*f + g*h < 2^64 := by
  have hab := AspisV8.QmCross.product_lt ha hb
  have hcd := AspisV8.QmCross.product_lt hc hd
  have hef := AspisV8.QmCross.product_lt he hf
  have hgh := AspisV8.QmCross.product_lt hg hh
  have h := AspisV8.QmCross.four_range hab hcd hef hgh
  have hw : AspisV8.QmCross.word = 2^64 := by
    norm_num [AspisV8.QmCross.word]
  rw [← hw]
  exact h

/-- Ten actual one-fold chunk representatives fit in the final U64
accumulator. The caller must separately prove each raw chunk is below
`4*P^2`; the lemma preserves that proof boundary. -/
theorem tenPartialChunks_fit (chunks : Fin 10 → Nat)
    (hchunks : ∀ i, chunks i < 4*P^2) :
    (∑ i : Fin 10, AspisV8.QmCross.partialFold (chunks i)) < 2^37 := by
  have hsum :
      (∑ i : Fin 10, AspisV8.QmCross.partialFold (chunks i)) ≤
        ∑ _i : Fin 10, 5*P :=
    Finset.sum_le_sum fun i _ =>
      Nat.le_of_lt (AspisV8.QmCross.partial_range (n := 4) (hchunks i))
  have hcap : (∑ _i : Fin 10, 5*P) < 2^37 := by
    norm_num [P, AspisV8.QmCross.p]
  omega

/-- The ten source chunks must be connected to this generic list bridge by
named chunk boundaries; no generated recurrence is unfolded here. -/
theorem partialChunks_mod (chunks : List Nat) :
    (chunks.map AspisV8.QmCross.partialFold).sum % P = chunks.sum % P :=
  AspisV8.QmCross.partial_list chunks

/-- The actual mixed-term lookup remains inside the captured 48-word row for
all twelve mixed coefficients and every legal four-slot choice. -/
theorem mixedC2Index_lt48 (j : Fin 12) (slot : Usize)
    (hslot : slot.val < 4) :
    16 * (j.val / 4) + 4 * slot.val + j.val % 4 < 48 := by
  have hj := j.isLt
  omega

/-- The inner source lookup uses the actual four-limb coordinate. -/
theorem limbIndex_lt4 (L : Usize) (hL : L.val < 4) : L.val < 4 := hL

/-- Exact c1 contribution represented by the requested source theorem. -/
private def c1Dot (L : Fin 4) (c1 : Array U32 26#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients) : Nat :=
  ∑ i : Fin 26,
    (arrayAt c1 i).val * (arrayAt (arrayAt p.c1_limbs i) L).val

/-- Exact mixed contribution with the selected query-arithmetic c2 layout. -/
private def mixedDot (slot : Usize) (hslot : slot.val < 4) (L : Fin 4)
    (c2 : Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients) : Nat :=
  ∑ j : Fin 12,
    (arrayAt c2 ⟨16 * (j.val / 4) + 4 * slot.val + j.val % 4,
      mixedC2Index_lt48 j slot hslot⟩).val *
    (arrayAt (arrayAt p.mixed j) L).val

/-- The public arithmetic expression is a 38-term sum: 26 ordinary c1 terms
and 12 mixed terms. This is a statement-level definition, not yet a theorem
about the captured function. -/
private def selected38Sum (L : Fin 4) (slot : Usize) (hslot : slot.val < 4)
    (c1 : Array U32 26#usize) (c2 : Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients) : Nat :=
  c1Dot L c1 p + mixedDot slot hslot L c2 p

/-- A canonical operand pair is an ordinary natural product; the captured
U64 wrapping multiply is handled through R161 after this bound. -/
theorem canonicalProduct_lt (a b : Nat) (ha : a < P) (hb : b < P) :
    a * b < P * P :=
  AspisV8.QmCross.product_lt ha hb

/-- The captured ordinary reducer is the frozen selected reducer, using the
same explicit-body unfolding pattern already checked for R391/R415. -/
theorem selected_reduce_u64_eq_frozen (x : U64) :
    AspisR614SelectedCombineBeta.aspis_core.field.reduce_u64 x =
      AspisR156FullFreeze.aspis_core.field.reduce_u64 x := by
  simp only [AspisR614SelectedCombineBeta.aspis_core.field.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.P]

/-- The captured M31 wrapper is connected to that exact ordinary reducer. -/
theorem selected_m31_reduce_u64_eq_frozen (x : U64) :
    AspisR614SelectedCombineBeta.aspis_core.field.M31.reduce_u64 x =
      AspisR156FullFreeze.aspis_core.field.M31.reduce_u64 x := by
  simp only [AspisR614SelectedCombineBeta.aspis_core.field.M31.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.M31.reduce_u64,
    AspisR614SelectedCombineBeta.aspis_core.field.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.P]

/-- R161 supplies canonical success once the actual wrapper equality is
established. This theorem has no input bound. -/
theorem selected_m31_reduce_u64_success (x : U64) :
    ∃ z : U32,
      AspisR614SelectedCombineBeta.aspis_core.field.M31.reduce_u64 x = .ok z ∧
      z.val = x.val % P ∧ z.val < P := by
  obtain ⟨z, hz, hv, hc⟩ :=
    AspisV8R19.R161WrappedMulExecution.reducer_success x
  refine ⟨z, ?_, hv, hc⟩
  rw [selected_m31_reduce_u64_eq_frozen]
  simp only [AspisR156FullFreeze.aspis_core.field.M31.reduce_u64,
    hz, bind_tc_ok]

/-- The pinned widening conversion is the typed U64 cast for every U32
input; this exposes the exact operation consumed by each source product. -/
theorem selected_from_u32_eq_cast (x : U32) :
    core.convert.num.FromU64U32.from x = UScalar.cast .U64 x := by
  rfl

/-- A converted pair of arbitrary U32 words multiplies exactly in the raw U64
word when interpreted by the selected wrapping multiply. -/
theorem selected_u32_mul64_val (a b : U32) :
    (Std.U64.wrapping_mul (core.convert.num.FromU64U32.from a)
      (core.convert.num.FromU64U32.from b)).val = a.val * b.val := by
  rw [selected_from_u32_eq_cast, selected_from_u32_eq_cast]
  change (U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val = _
  rw [AspisV8R19.R161WrappedMulExecution.mul64_val,
    cast_widen_value, cast_widen_value]
  rw [cast_widen_value, cast_widen_value]
  have hproduct : a.val * b.val < (2^32) * (2^32) :=
    Nat.mul_lt_mul_of_lt_of_lt a.bv.isLt b.bv.isLt
  exact hproduct

private def selectedProduct (a b : U32) : U64 :=
  Std.U64.wrapping_mul (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from b)

private def selectedAdd (a b : U64) : U64 := Std.U64.wrapping_add a b

private theorem selected_add_val (a b : U64) (h : a.val + b.val < 2^64) :
    (selectedAdd a b).val = a.val + b.val := by
  change (U64.wrapping_add a b).val = a.val + b.val
  exact AspisV8R19.R159WideBaseExecution.add64_val a b h

/-- Exact value of the source's first two products and their wrapping sum,
under the same canonical-input condition used by the 38-term theorem. -/
theorem selected_two_products_val (a b c d : U32)
    (ha : a.val < P) (hb : b.val < P)
    (hc : c.val < P) (hd : d.val < P) :
    (selectedAdd (selectedProduct a b) (selectedProduct c d)).val =
      a.val*b.val + c.val*d.val := by
  have hp1 := canonicalProduct_lt a.val b.val ha hb
  have hp2 := canonicalProduct_lt c.val d.val hc hd
  have hsum : a.val*b.val + c.val*d.val < 2^64 := by
    have h4 := fourProducts_lt_u64 a.val b.val c.val d.val 0 0 0 0
      ha hb hc hd (by norm_num [P, AspisV8.QmCross.p])
      (by norm_num [P, AspisV8.QmCross.p])
      (by norm_num [P, AspisV8.QmCross.p])
      (by norm_num [P, AspisV8.QmCross.p])
    omega
  have hrawsum : (selectedProduct a b).val + (selectedProduct c d).val < 2^64 := by
    change (Std.U64.wrapping_mul (core.convert.num.FromU64U32.from a)
      (core.convert.num.FromU64U32.from b)).val +
      (Std.U64.wrapping_mul (core.convert.num.FromU64U32.from c)
      (core.convert.num.FromU64U32.from d)).val < 2^64
    rw [selected_u32_mul64_val, selected_u32_mul64_val]
    exact hsum
  change (U64.wrapping_add (selectedProduct a b) (selectedProduct c d)).val = _
  rw [AspisV8R19.R159WideBaseExecution.add64_val _ _ hrawsum]
  simpa only [selectedProduct, selected_u32_mul64_val]

/-- Exact value of one four-product source chunk before `reduce_chunk`.
This named interface follows the left-associated wrapping additions in the
captured body and uses only the four canonical operand bounds. -/
theorem selected_four_products_val (a b c d e f g h : U32)
    (ha : a.val < P) (hb : b.val < P)
    (hc : c.val < P) (hd : d.val < P)
    (he : e.val < P) (hf : f.val < P)
    (hg : g.val < P) (hh : h.val < P) :
    (selectedAdd
      (selectedAdd (selectedAdd (selectedProduct a b) (selectedProduct c d))
        (selectedProduct e f)) (selectedProduct g h)).val =
      a.val*b.val + c.val*d.val + e.val*f.val + g.val*h.val := by
  have h4 := fourProducts_lt_u64 a.val b.val c.val d.val e.val f.val g.val h.val
    ha hb hc hd he hf hg hh
  have hp1 : (selectedProduct a b).val = a.val*b.val := selected_u32_mul64_val a b
  have hp2 : (selectedProduct c d).val = c.val*d.val := selected_u32_mul64_val c d
  have hp3 : (selectedProduct e f).val = e.val*f.val := selected_u32_mul64_val e f
  have hp4 : (selectedProduct g h).val = g.val*h.val := selected_u32_mul64_val g h
  have h12 : (selectedAdd (selectedProduct a b) (selectedProduct c d)).val =
      a.val*b.val + c.val*d.val := by
    exact selected_two_products_val a b c d ha hb hc hd
  have h123 : (selectedAdd
      (selectedAdd (selectedProduct a b) (selectedProduct c d))
      (selectedProduct e f)).val =
      a.val*b.val + c.val*d.val + e.val*f.val := by
    have hbound :
        (selectedAdd (selectedProduct a b) (selectedProduct c d)).val +
          (selectedProduct e f).val < 2^64 := by
      rw [h12, hp3]
      omega
    calc
      _ = (selectedAdd (selectedProduct a b) (selectedProduct c d)).val +
          (selectedProduct e f).val := selected_add_val _ _ hbound
      _ = a.val*b.val + c.val*d.val + e.val*f.val := by rw [h12, hp3]
  have hbound :
      (selectedAdd
        (selectedAdd (selectedProduct a b) (selectedProduct c d))
        (selectedProduct e f)).val + (selectedProduct g h).val < 2^64 := by
    rw [h123, hp4]
    omega
  calc
    _ = (selectedAdd
        (selectedAdd (selectedProduct a b) (selectedProduct c d))
        (selectedProduct e f)).val + (selectedProduct g h).val :=
          selected_add_val _ _ hbound
    _ = a.val*b.val + c.val*d.val + e.val*f.val + g.val*h.val := by
      rw [h123, hp4]

/-- The actual frozen conversion of the captured M31 prime is its U64 cast.
This reuses the exact typed conversion/cast equalities from R164. -/
theorem selected_from_prime :
    core.convert.num.FromU64U32.from (2147483647#u32) =
      UScalar.cast .U64 AspisR156FullFreeze.aspis_core.field.P := by
  have hp : (2147483647#u32 : U32) =
      AspisR156FullFreeze.aspis_core.field.P := by
    simp only [AspisR156FullFreeze.aspis_core.field.P]
  rw [hp]
  exact (AspisV8R19.R164ProductExecution.prime_from).trans
    AspisV8R19.R164ProductExecution.prime_word.symm

/-- The captured helper is exactly the selected release's first Mersenne
fold. Its conversion and result handling are discharged by the actual generated
body, not by assuming helper success. -/
theorem selected_reduce_chunk_eq_fold (x : U64) :
    AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk x =
      .ok (AspisV8R19.R161WrappedMulExecution.wrappedFold x) := by
  simp only [AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk,
    lift, bind_tc_ok, AspisV8R19.R161WrappedMulExecution.wrappedFold]
  rw [selected_from_prime]
  rfl

/-- With the exact source chunk bound, the captured helper returns the actual
one-fold representative below `5P`. -/
theorem selected_reduce_chunk_success (x : U64) (hx : x.val < 4 * P * P) :
    ∃ z : U64,
      AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk x = .ok z ∧
      z.val = AspisV8R19.PartialProduct.foldOnce x.val ∧ z.val < 5 * P := by
  have hval :
      (AspisV8R19.R161WrappedMulExecution.wrappedFold x).val =
        AspisV8R19.PartialProduct.foldOnce x.val := by
    rw [AspisV8R19.R161WrappedMulExecution.wrappedFold_val]
    unfold AspisV8R17.RawReducer.foldBits
    exact AspisV8R19.PartialProduct.source_fold x.val
  have hbound :
      AspisV8R19.PartialProduct.foldOnce x.val < 5 * P := by
    have hq := AspisV8.QmCross.partial_range (n := 4) hx
    simpa only [AspisV8.QmCross.partialFold, AspisV8.QmCross.p,
      AspisV8R19.PartialProduct.foldOnce, AspisV8R19.PartialProduct.p, P] using hq
  refine ⟨AspisV8R19.R161WrappedMulExecution.wrappedFold x, ?_, hval, ?_⟩
  · exact selected_reduce_chunk_eq_fold x
  · rw [hval]
    exact hbound

/-- The generated one-fold helper returns a residue-preserving chunk value.
The caller supplies the source-derived raw word and its mathematical sum;
this isolates chunk arithmetic from the generated 38-term continuation. -/
theorem selected_chunk_residue (raw : U64) (rawSum : Nat)
    (hraw : raw.val = rawSum) (hbound : rawSum < 4 * P * P) :
    ∃ z : U64,
      AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk raw = .ok z ∧
      z.val < 5 * P ∧ z.val % P = rawSum % P := by
  obtain ⟨z, hz, hv, hb⟩ := selected_reduce_chunk_success raw (by omega)
  refine ⟨z, hz, hb, ?_⟩
  rw [hv, hraw]
  change AspisV8R19.PartialProduct.foldOnce rawSum %
    AspisV8R19.PartialProduct.p = rawSum % AspisV8R19.PartialProduct.p
  exact AspisV8R19.PartialProduct.partial_mod rawSum

/-- A four-term group of the captured multiply/add/reduce pipeline returns an
actual one-fold chunk with the expected residue and the source-derived bound.
The eventual generated-body proof must instantiate this at each named group. -/
theorem selected_four_product_chunk (a b c d e f g h : U32)
    (ha : a.val < P) (hb : b.val < P)
    (hc : c.val < P) (hd : d.val < P)
    (he : e.val < P) (hf : f.val < P)
    (hg : g.val < P) (hh : h.val < P) :
    ∃ z : U64,
      AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk
        (selectedAdd
          (selectedAdd (selectedAdd (selectedProduct a b) (selectedProduct c d))
            (selectedProduct e f)) (selectedProduct g h)) = .ok z ∧
      z.val < 5 * P ∧
      z.val % P =
        (a.val*b.val + c.val*d.val + e.val*f.val + g.val*h.val) % P := by
  have hval := selected_four_products_val a b c d e f g h
    ha hb hc hd he hf hg hh
  have hrange : a.val*b.val + c.val*d.val + e.val*f.val + g.val*h.val <
      4 * P * P := by
    have h1 : a.val*b.val < P^2 := by
      simpa [P, AspisV8.QmCross.p] using AspisV8.QmCross.product_lt ha hb
    have h2 : c.val*d.val < P^2 := by
      simpa [P, AspisV8.QmCross.p] using AspisV8.QmCross.product_lt hc hd
    have h3 : e.val*f.val < P^2 := by
      simpa [P, AspisV8.QmCross.p] using AspisV8.QmCross.product_lt he hf
    have h4 : g.val*h.val < P^2 := by
      simpa [P, AspisV8.QmCross.p] using AspisV8.QmCross.product_lt hg hh
    have hs : a.val*b.val + c.val*d.val + e.val*f.val + g.val*h.val <
        4 * P^2 := by omega
    calc
      _ < 4 * P^2 := hs
      _ = 4 * P * P := by ring
  exact selected_chunk_residue _ _ hval hrange

#print axioms fourProducts_lt_u64
#print axioms selected_index_ok
#print axioms tenPartialChunks_fit
#print axioms partialChunks_mod
#print axioms mixedC2Index_lt48
#print axioms limbIndex_lt4
#print axioms canonicalProduct_lt
#print axioms selected_reduce_u64_eq_frozen
#print axioms selected_m31_reduce_u64_eq_frozen
#print axioms selected_m31_reduce_u64_success
#print axioms selected_from_u32_eq_cast
#print axioms selected_u32_mul64_val
#print axioms selected_two_products_val
#print axioms selected_four_products_val
#print axioms selected_from_prime
#print axioms selected_reduce_chunk_eq_fold
#print axioms selected_reduce_chunk_success
#print axioms selected_chunk_residue
#print axioms selected_four_product_chunk

/-! The remaining actual-source theorem is the full 38-term conclusion above.
Before proving it, establish the exact captured `reduce_chunk` success/fold
bridge while preserving its conversion errors, then expose the ten source
chunk boundaries and discharge the actual array-index errors from the stated
bounds. The generated 38-term recurrence is not unfolded here. -/

end AspisV8R19.R616MixedLimbExecution
