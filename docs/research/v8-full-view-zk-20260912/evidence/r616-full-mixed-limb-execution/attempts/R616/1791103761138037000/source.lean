
import AspisR515SharedGamma.QmCrossRange
import AspisV8R19.R161WrappedMulExecution
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

open scoped BigOperators

private abbrev P : Nat := AspisV8.QmCross.p

/-- Read a dependent Aeneas array at a proof-carrying natural index. -/
private def arrayAt {α : Type} {n : Usize} (a : Aeneas.Std.Array α n)
    (i : Fin n.val) : α :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

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
    norm_num [P, AspisV8.SharedGammaDots.p]
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
    a * b < P * P := by
  calc
    a * b < P * b := Nat.mul_lt_mul_of_pos_right ha (Nat.zero_lt_of_lt hb)
    _ < P * P := Nat.mul_lt_mul_left P hb

/-- The captured ordinary reducer is the frozen selected reducer, using the
same explicit-body unfolding pattern already checked for R391/R415. -/
theorem selected_reduce_u64_eq_frozen (x : U64) :
    AspisR614SelectedCombineBeta.aspis_core.field.reduce_u64 x =
      AspisR156FullFreeze.aspis_core.field.reduce_u64 x := by
  simp only [AspisR614SelectedCombineBeta.aspis_core.field.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.reduce_u64,
    AspisR614SelectedCombineBeta.aspis_core.field.P,
    AspisR156FullFreeze.aspis_core.field.P]

/-- The captured M31 wrapper is connected to that exact ordinary reducer. -/
theorem selected_m31_reduce_u64_eq_frozen (x : U64) :
    AspisR614SelectedCombineBeta.aspis_core.field.M31.reduce_u64 x =
      AspisR156FullFreeze.aspis_core.field.M31.reduce_u64 x := by
  simp only [AspisR614SelectedCombineBeta.aspis_core.field.M31.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.M31.reduce_u64,
    selected_reduce_u64_eq_frozen, bind_tc_ok]

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

/-- One source chunk is the actual release fold. This exact equality is the
remaining small source bridge to prove against the compiled generated body;
its result must preserve lift/conversion errors rather than assume success. -/
/-
 theorem selected_reduce_chunk_eq_fold (x : U64) :
    AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk x =
      .ok (AspisV8R19.R161WrappedMulExecution.wrappedFold x) := by
   -- Establish the captured u32-to-u64 conversion, then unfold only this
   -- two-mask/shift/add helper; no chunk recurrence is unfolded.
-/

/-- Actual source target, still unproved pending successful E translation,
focused Funs compilation, and root review of the generated syntax. Premises are
exactly coordinate/slot bounds and canonicality of all consumed words. -/
/-
 theorem r83_mixed_limb_execution
    (L slot : Usize) (c1 : Array U32 26#usize)
    (c2 : Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (hL : L.val < 4) (hslot : slot.val < 4)
    (hc1 : ∀ i : Fin 26, (arrayAt c1 i).val < P)
    (hc2 : ∀ i : Fin 48, (arrayAt c2 i).val < P)
    (hp1 : ∀ i : Fin 26, ∀ r : Fin 4,
      (arrayAt (arrayAt p.c1_limbs i) r).val < P)
    (hpm : ∀ i : Fin 12, ∀ r : Fin 4,
      (arrayAt (arrayAt p.mixed i) r).val < P) :
    ∃ z : AspisR614SelectedCombineBeta.aspis_core.field.M31,
      AspisR614SelectedCombineBeta.query_arithmetic.r83_mixed_limb
        L c1 c2 slot p = .ok z ∧ z.val < P ∧
      z.val = selected38Sum ⟨L.val, hL⟩ slot hslot c1 c2 p % P := by
   -- Proof pending: ten named source chunk steps, with captured error branches
   -- discharged only from the explicit bounds above.
-/

end AspisV8R19.R616MixedLimbExecution
