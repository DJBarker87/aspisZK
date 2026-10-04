
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

private theorem usizeSize_gt_38 : 38 < UScalar.size .Usize := by
  rcases System.Platform.numBits_eq with hp | hp <;>
    simp [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq, hp] <;> omega

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
  simp only [
    show (16#usize : Usize).val = 16 from rfl,
    show (4#usize : Usize).val = 4 from rfl]
  have hdivsmall : j.val / 4 ≤ 2 := by omega
  have hremsmall : j.val % 4 < 4 := by omega
  have hsize : Usize.max + 1 = UScalar.size .Usize := by
    simp [Usize.max, Usize.size, Usize.numBits]
  have hm16 : 16 * (j.val / 4) < UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    have hc : 16 * (j.val / 4) ≤ UScalar.cMax .Usize := by scalar_tac
    omega
  have hm4 : 4 * slot.val < UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    have hc : 4 * slot.val ≤ UScalar.cMax .Usize := by scalar_tac
    omega
  have ha : 16 * (j.val / 4) + 4 * slot.val < UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    have hc : 16 * (j.val / 4) + 4 * slot.val ≤ UScalar.cMax .Usize := by scalar_tac
    omega
  have hall : 16 * (j.val / 4) + 4 * slot.val + j.val % 4 <
      UScalar.size .Usize := by
    have hmax := Usize.cMax_bound
    have hc : 16 * (j.val / 4) + 4 * slot.val + j.val % 4 ≤
        UScalar.cMax .Usize := by scalar_tac
    omega
  rw [Nat.mod_eq_of_lt hm16, Nat.mod_eq_of_lt hm4, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hall]

/-- The complete checked mixed-row lookup succeeds at the exact source index,
including both checked div/rem binds and the array-out-of-bounds branch. -/
theorem selected_mixed_c2_access (c2 : Aeneas.Std.Array U32 48#usize)
    (j slot : Usize) (hj : j.val < 12) (hslot : slot.val < 4) :
    ∃ x : U32,
      (do let index ← selected_mixed_index j slot
          Aeneas.Std.Array.index_usize c2 index) = .ok x ∧
      x = arrayAt c2 ⟨16 * (j.val / 4) + 4 * slot.val + j.val % 4,
        by
          change 16 * (j.val / 4) + 4 * slot.val + j.val % 4 < 48
          have ⟨hpartition, hrem⟩ := AspisV8R19.R489WordArithmetic.div_rem_partition j
          have hqsmall : j.val / 4 ≤ 2 := by omega
          omega⟩ := by
  obtain ⟨index, hindex, hvalue⟩ := selected_mixed_index_spec j slot hj hslot
  have hformula : 16 * (j.val / 4) + 4 * slot.val + j.val % 4 < 48 := by
    have ⟨hpartition, hrem⟩ := AspisV8R19.R489WordArithmetic.div_rem_partition j
    have hqsmall : j.val / 4 ≤ 2 := by omega
    omega
  have hindex_bound : index.val < 48 := by
    rw [hvalue]
    exact hformula
  have haccess := selected_index_ok c2 index hindex_bound
  refine ⟨arrayAt c2 ⟨index.val, hindex_bound⟩, ?_, ?_⟩
  · simp only [hindex, bind_tc_ok]
    exact haccess
  · congr 1
    apply Fin.ext
    exact hvalue

/-- One captured mixed-term lookup prefix, with the same literal `26+j-26`
counter construction used by each of the twelve actual generated source
segments. This keeps the subtraction and checked div/rem/index Result chain
visible; only the proved in-range instance returns `.ok`. -/
private def selected_source_mixed_c2_access
    (c2 : Aeneas.Std.Array U32 48#usize) (j : Fin 12) (slot : Usize) :
    Result U32 := do
  let sourceJ ← lift (core.num.Usize.wrapping_sub
    ((26 + j.val)#usize) 26#usize)
  let index ← selected_mixed_index sourceJ slot
  Aeneas.Std.Array.index_usize c2 index

theorem selected_source_mixed_c2_access_ok
    (c2 : Aeneas.Std.Array U32 48#usize) (j : Fin 12) (slot : Usize)
    (hslot : slot.val < 4) :
    ∃ x : U32,
      selected_source_mixed_c2_access c2 j slot = .ok x ∧
      x = arrayAt c2 ⟨16 * (j.val / 4) + 4 * slot.val + j.val % 4,
        by
          change 16 * (j.val / 4) + 4 * slot.val + j.val % 4 < 48
          have hquot : j.val / 4 ≤ 2 := by omega
          have hrem : j.val % 4 < 4 := Nat.mod_lt _ (by omega)
          omega⟩ := by
  have hsubval :
      (core.num.Usize.wrapping_sub ((26 + j.val)#usize) 26#usize).val = j.val := by
    rw [core.num.Usize.wrapping_sub_val_eq]
    have h38 := usizeSize_gt_38
    have hno : 26 + j.val < UScalar.size .Usize := by omega
    have hfirst : ((26 + j.val)#usize).val = 26 + j.val := by
      simp only [UScalar.ofNatCore_val_eq]
    have h26 : (26#usize : Usize).val = 26 := by rfl
    rw [hfirst, h26]
    have hshift : 26 + j.val + (UScalar.size .Usize - 26) =
        j.val + UScalar.size .Usize := by omega
    rw [hshift, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  let sourceJ := core.num.Usize.wrapping_sub ((26 + j.val)#usize) 26#usize
  have hsourceBound : sourceJ.val < 12 := by rw [hsubval]; exact j.isLt
  obtain ⟨x, hx, hvalue⟩ :=
    selected_mixed_c2_access c2 sourceJ slot hsourceBound hslot
  have hfin :
      (⟨16 * (sourceJ.val / 4) + 4 * slot.val + sourceJ.val % 4,
        by
          have hq : sourceJ.val / 4 ≤ 2 := by omega
          have hr : sourceJ.val % 4 < 4 := Nat.mod_lt _ (by omega)
          omega⟩ : Fin 48) =
      ⟨16 * (j.val / 4) + 4 * slot.val + j.val % 4,
        by
          change 16 * (j.val / 4) + 4 * slot.val + j.val % 4 < 48
          have hq : j.val / 4 ≤ 2 := by omega
          have hr : j.val % 4 < 4 := Nat.mod_lt _ (by omega)
          omega⟩ := by
    apply Fin.ext
    simp only [sourceJ, hsubval]
  refine ⟨x, ?_, ?_⟩
  · change (do
      let sourceJ ← lift (core.num.Usize.wrapping_sub ((26 + j.val)#usize) 26#usize)
      let index ← selected_mixed_index sourceJ slot
      Aeneas.Std.Array.index_usize c2 index) = .ok x
    simp only [lift, bind_tc_ok]
    exact hx
  · exact hvalue.trans (congrArg (arrayAt c2) hfin)

/-- The source's complete mixed coefficient read and product, factored at the
first c2 result. This keeps both literal counter subtractions and the second
checked row/lane accesses, while exposing the exact product consumed by the
following U64 accumulator bind. -/
private def selected_source_mixed_product
    (c2 : Aeneas.Std.Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L slot : Usize) (j : Fin 12) : Result U64 := do
  let c2word ← selected_source_mixed_c2_access c2 j slot
  let c2word64 ← lift (core.convert.num.FromU64U32.from c2word)
  let mixedRowIndex ← lift (core.num.Usize.wrapping_sub
    ((26 + j.val)#usize) 26#usize)
  let mixedRow ← Aeneas.Std.Array.index_usize p.mixed mixedRowIndex
  let coefficient ← Aeneas.Std.Array.index_usize mixedRow L
  let coefficientWord ← lift (core.convert.num.FromU64U32.from coefficient)
  lift (Std.U64.wrapping_mul c2word64 coefficientWord)

/-- Literal-counter form of the selected mixed term, matching the actual
straight-line source where `sourceK` is 26#usize through 37#usize. -/
private def selected_source_mixed_product_literal
    (c2 : Aeneas.Std.Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L slot sourceK : Usize) : Result U64 := do
  let sourceJ ← lift (core.num.Usize.wrapping_sub sourceK 26#usize)
  let q ← sourceJ / 4#usize
  let i ← lift (Usize.wrapping_mul 16#usize q)
  let s ← lift (Usize.wrapping_mul 4#usize slot)
  let a ← lift (i.wrapping_add s)
  let r ← sourceJ % 4#usize
  let index ← lift (a.wrapping_add r)
  let c2word ← Aeneas.Std.Array.index_usize c2 index
  let c2word64 ← lift (core.convert.num.FromU64U32.from c2word)
  let mixedRowIndex ← lift (core.num.Usize.wrapping_sub sourceK 26#usize)
  let mixedRow ← Aeneas.Std.Array.index_usize p.mixed mixedRowIndex
  let coefficient ← Aeneas.Std.Array.index_usize mixedRow L
  let coefficientWord ← lift (core.convert.num.FromU64U32.from coefficient)
  lift (Std.U64.wrapping_mul c2word64 coefficientWord)

/-- Continuation-preserving factorization using the exact literal counter in
R614's mixed source terms; this matches without arithmetic unification. -/
theorem source_mixed_product_literal_bind
    {α : Type} (c2 : Aeneas.Std.Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L slot sourceK : Usize) (k : U64 → Result α) :
    (do
      let sourceJ ← lift (core.num.Usize.wrapping_sub sourceK 26#usize)
      let q ← sourceJ / 4#usize
      let i ← lift (Usize.wrapping_mul 16#usize q)
      let s ← lift (Usize.wrapping_mul 4#usize slot)
      let a ← lift (i.wrapping_add s)
      let r ← sourceJ % 4#usize
      let index ← lift (a.wrapping_add r)
      let c2word ← Aeneas.Std.Array.index_usize c2 index
      let c2word64 ← lift (core.convert.num.FromU64U32.from c2word)
      let mixedRowIndex ← lift (core.num.Usize.wrapping_sub sourceK 26#usize)
      let mixedRow ← Aeneas.Std.Array.index_usize p.mixed mixedRowIndex
      let coefficient ← Aeneas.Std.Array.index_usize mixedRow L
      let coefficientWord ← lift (core.convert.num.FromU64U32.from coefficient)
      let product ← lift (Std.U64.wrapping_mul c2word64 coefficientWord)
      k product) =
    (do
      let product ← selected_source_mixed_product_literal c2 p L slot sourceK
      k product) := by
  simp only [selected_source_mixed_product_literal, bind_assoc_eq]

private def selected_source_c1_product
    (c1 : Aeneas.Std.Array U32 26#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L i : Usize) : Result U64 := do
  let word ← Aeneas.Std.Array.index_usize c1 i
  let word64 ← lift (core.convert.num.FromU64U32.from word)
  let row ← Aeneas.Std.Array.index_usize p.c1_limbs i
  let coefficient ← Aeneas.Std.Array.index_usize row L
  let coefficientWord ← lift (core.convert.num.FromU64U32.from coefficient)
  lift (Std.U64.wrapping_mul word64 coefficientWord)

theorem selected_source_c1_product_ok
    (c1 : Aeneas.Std.Array U32 26#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L i : Usize) (hL : L.val < 4) (hi : i.val < 26) :
    ∃ product : U64,
      selected_source_c1_product c1 p L i = .ok product ∧
      product.val =
        (Std.U64.wrapping_mul
          (core.convert.num.FromU64U32.from
            (arrayAt c1 ⟨i.val, by simpa only [show (26#usize : Usize).val = 26 from rfl] using hi⟩))
          (core.convert.num.FromU64U32.from
            (arrayAt
              (arrayAt p.c1_limbs ⟨i.val,
                by simpa only [show (26#usize : Usize).val = 26 from rfl] using hi⟩)
              ⟨L.val,
                by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩))).val := by
  have hiArray : i.val < (26#usize : Usize).val := by
    simpa only [show (26#usize : Usize).val = 26 from rfl] using hi
  have hLArray : L.val < (4#usize : Usize).val := by
    simpa only [show (4#usize : Usize).val = 4 from rfl] using hL
  have hc1 :
      Aeneas.Std.Array.index_usize c1 i =
        .ok (arrayAt c1 ⟨i.val, hiArray⟩) := by
    have hread := selected_index_ok c1 i hiArray
    simpa only [arrayAt] using hread
  have hrow :
      Aeneas.Std.Array.index_usize p.c1_limbs i =
        .ok (arrayAt p.c1_limbs ⟨i.val, hiArray⟩) := by
    have hread := selected_index_ok p.c1_limbs i hiArray
    simpa only [arrayAt] using hread
  have hcoef :
      Aeneas.Std.Array.index_usize (arrayAt p.c1_limbs ⟨i.val, hiArray⟩) L =
        .ok (arrayAt (arrayAt p.c1_limbs ⟨i.val, hiArray⟩) ⟨L.val, hLArray⟩) := by
    have hread := selected_index_ok
      (arrayAt p.c1_limbs ⟨i.val, hiArray⟩) L hLArray
    simpa only [arrayAt] using hread
  refine ⟨Std.U64.wrapping_mul
      (core.convert.num.FromU64U32.from (arrayAt c1 ⟨i.val, hiArray⟩))
      (core.convert.num.FromU64U32.from
        (arrayAt (arrayAt p.c1_limbs ⟨i.val, hiArray⟩) ⟨L.val, hLArray⟩)), ?_, ?_⟩
  · simp only [selected_source_c1_product, bind_tc_ok, hc1, hrow, hcoef, lift]
  · rfl

/-- The first straight-line c1 term is definitionally the factored actual
source product computation used by the main-body proof. -/
private theorem source_c1_term0_eq_factored
    (c1 : Aeneas.Std.Array U32 26#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L : Usize) :
    (do
      let word ← Aeneas.Std.Array.index_usize c1 0#usize
      let word64 ← lift (core.convert.num.FromU64U32.from word)
      let row ← Aeneas.Std.Array.index_usize p.c1_limbs 0#usize
      let coefficient ← Aeneas.Std.Array.index_usize row L
      let coefficient64 ← lift (core.convert.num.FromU64U32.from coefficient)
      lift (Std.U64.wrapping_mul word64 coefficient64)) =
      selected_source_c1_product c1 p L 0#usize := by
  rfl

/-- Monad-context form of the captured ordinary product prefix. It lets the
actual straight-line source chain be factored one term at a time without
changing the continuation or dropping a Result branch. -/
theorem source_c1_product_bind
    {α : Type} (c1 : Aeneas.Std.Array U32 26#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L i : Usize) (k : U64 → Result α) :
    (do
      let word ← Aeneas.Std.Array.index_usize c1 i
      let word64 ← lift (core.convert.num.FromU64U32.from word)
      let row ← Aeneas.Std.Array.index_usize p.c1_limbs i
      let coefficient ← Aeneas.Std.Array.index_usize row L
      let coefficient64 ← lift (core.convert.num.FromU64U32.from coefficient)
      let product ← lift (Std.U64.wrapping_mul word64 coefficient64)
      k product) =
    (do
      let product ← selected_source_c1_product c1 p L i
      k product) := by
  simp only [selected_source_c1_product, bind_assoc_eq]

/-- Continuation-preserving factorization of one captured mixed term. The
index arithmetic and both `26+j-26` operations stay in the actual sequence;
only the source-local term is named. -/
theorem source_mixed_product_bind
    {α : Type} (c2 : Aeneas.Std.Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L slot : Usize) (j : Fin 12) (k : U64 → Result α) :
    (do
      let sourceJ ← lift (core.num.Usize.wrapping_sub ((26 + j.val)#usize) 26#usize)
      let q ← sourceJ / 4#usize
      let i ← lift (Usize.wrapping_mul 16#usize q)
      let s ← lift (Usize.wrapping_mul 4#usize slot)
      let a ← lift (i.wrapping_add s)
      let r ← sourceJ % 4#usize
      let index ← lift (a.wrapping_add r)
      let c2word ← Aeneas.Std.Array.index_usize c2 index
      let c2word64 ← lift (core.convert.num.FromU64U32.from c2word)
      let mixedRowIndex ← lift (core.num.Usize.wrapping_sub ((26 + j.val)#usize) 26#usize)
      let mixedRow ← Aeneas.Std.Array.index_usize p.mixed mixedRowIndex
      let coefficient ← Aeneas.Std.Array.index_usize mixedRow L
      let coefficientWord ← lift (core.convert.num.FromU64U32.from coefficient)
      let product ← lift (Std.U64.wrapping_mul c2word64 coefficientWord)
      k product) =
    (do
      let product ← selected_source_mixed_product c2 p L slot j
      k product) := by
  simp only [selected_source_mixed_product, selected_source_mixed_c2_access,
    selected_mixed_index, bind_assoc_eq]

theorem selected_source_mixed_product_ok
    (c2 : Aeneas.Std.Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L slot : Usize) (j : Fin 12)
    (hL : L.val < 4) (hslot : slot.val < 4) :
    ∃ product : U64,
      selected_source_mixed_product c2 p L slot j = .ok product ∧
      product.val =
        (Std.U64.wrapping_mul
          (core.convert.num.FromU64U32.from
            (arrayAt c2 ⟨16 * (j.val / 4) + 4 * slot.val + j.val % 4,
              by
                change 16 * (j.val / 4) + 4 * slot.val + j.val % 4 < 48
                have hquot : j.val / 4 ≤ 2 := by omega
                have hrem : j.val % 4 < 4 := Nat.mod_lt _ (by omega)
                omega⟩))
          (core.convert.num.FromU64U32.from
            (arrayAt (arrayAt p.mixed j) ⟨L.val,
              by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩))).val := by
  obtain ⟨c2word, hc2, hc2value⟩ :=
    selected_source_mixed_c2_access_ok c2 j slot hslot
  have hsubval :
      (core.num.Usize.wrapping_sub ((26 + j.val)#usize) 26#usize).val = j.val := by
    rw [core.num.Usize.wrapping_sub_val_eq]
    have h38 := usizeSize_gt_38
    have hno : 26 + j.val < UScalar.size .Usize := by omega
    have hfirst : ((26 + j.val)#usize).val = 26 + j.val := by
      simp only [UScalar.ofNatCore_val_eq]
    have h26 : (26#usize : Usize).val = 26 := by rfl
    rw [hfirst, h26]
    have hshift : 26 + j.val + (UScalar.size .Usize - 26) =
        j.val + UScalar.size .Usize := by omega
    rw [hshift, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  let sourceJ := core.num.Usize.wrapping_sub ((26 + j.val)#usize) 26#usize
  have hsourceBound : sourceJ.val < 12 := by rw [hsubval]; exact j.isLt
  have hsourceArrayBound : sourceJ.val < (12#usize : Usize).val := by
    simpa only [show (12#usize : Usize).val = 12 from rfl] using hsourceBound
  have hrow :
      Aeneas.Std.Array.index_usize p.mixed sourceJ =
        .ok (arrayAt p.mixed j) := by
    rw [selected_index_ok p.mixed sourceJ hsourceArrayBound]
    apply congrArg Result.ok
    simp only [arrayAt, sourceJ, hsubval]
  have hLidx : L.val < (4#usize : Usize).val := by
    simpa only [show (4#usize : Usize).val = 4 from rfl] using hL
  have hcoef :
      Aeneas.Std.Array.index_usize (arrayAt p.mixed j) L =
        .ok (arrayAt (arrayAt p.mixed j) ⟨L.val, hLidx⟩) := by
    have hread := selected_index_ok (arrayAt p.mixed j) L hLidx
    simpa only [arrayAt] using hread
  refine ⟨Std.U64.wrapping_mul
    (core.convert.num.FromU64U32.from c2word)
    (core.convert.num.FromU64U32.from
      (arrayAt (arrayAt p.mixed j) ⟨L.val, hLidx⟩)), ?_, ?_⟩
  · simp only [selected_source_mixed_product, hc2, bind_tc_ok, sourceJ,
      lift, hrow, hcoef]
  · rw [hc2value]

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

/-- The source-shaped mixed read fragment produces the ordinary natural
product of its selected c2 word and mixed coefficient after the exact U32 to
U64 conversions. This is the first actual query-arithmetic term connected to
the source body; chunk accumulation remains a separate obligation. -/
theorem selected_source_mixed_product_value
    (c2 : Aeneas.Std.Array U32 48#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L slot : Usize) (j : Fin 12)
    (hL : L.val < 4) (hslot : slot.val < 4) :
    ∃ product : U64,
      selected_source_mixed_product c2 p L slot j = .ok product ∧
      product.val =
        (arrayAt c2 ⟨16 * (j.val / 4) + 4 * slot.val + j.val % 4,
          mixedC2Index_lt48 j slot hslot⟩).val *
        (arrayAt (arrayAt p.mixed j) ⟨L.val,
          by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩).val := by
  obtain ⟨product, hrun, hvalue⟩ :=
    selected_source_mixed_product_ok c2 p L slot j hL hslot
  refine ⟨product, hrun, ?_⟩
  rw [hvalue, selected_u32_mul64_val]

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


/-- First four-term chunk, copied from the captured R614 body and factored
through the exact c1 source-product helper while retaining its continuation. -/
theorem first_c1_four_source_chunk_bind
    {α : Type} (c1 : Aeneas.Std.Array U32 26#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L : Usize) (k : U64 → Result α) :
    (do
      let i ← Array.index_usize c1 0#usize
      let i1 ← lift (core.convert.num.FromU64U32.from i)
      let a ← Array.index_usize p.c1_limbs 0#usize
      let i2 ← Array.index_usize a L
      let i3 ← lift (core.convert.num.FromU64U32.from i2)
      let i4 ← lift (Std.U64.wrapping_mul i1 i3)
      let i5 ← Array.index_usize c1 1#usize
      let i6 ← lift (core.convert.num.FromU64U32.from i5)
      let a1 ← Array.index_usize p.c1_limbs 1#usize
      let i7 ← Array.index_usize a1 L
      let i8 ← lift (core.convert.num.FromU64U32.from i7)
      let i9 ← lift (Std.U64.wrapping_mul i6 i8)
      let i10 ← lift (core.num.U64.wrapping_add i4 i9)
      let i11 ← Array.index_usize c1 2#usize
      let i12 ← lift (core.convert.num.FromU64U32.from i11)
      let a2 ← Array.index_usize p.c1_limbs 2#usize
      let i13 ← Array.index_usize a2 L
      let i14 ← lift (core.convert.num.FromU64U32.from i13)
      let i15 ← lift (Std.U64.wrapping_mul i12 i14)
      let i16 ← lift (core.num.U64.wrapping_add i10 i15)
      let i17 ← Array.index_usize c1 3#usize
      let i18 ← lift (core.convert.num.FromU64U32.from i17)
      let a3 ← Array.index_usize p.c1_limbs 3#usize
      let i19 ← Array.index_usize a3 L
      let i20 ← lift (core.convert.num.FromU64U32.from i19)
      let i21 ← lift (Std.U64.wrapping_mul i18 i20)
      let i22 ← lift (core.num.U64.wrapping_add i16 i21)
      let i23 ← AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk i22
      
      k i23) =
    (do
      let i4 ← selected_source_c1_product c1 p L 0#usize
      let i9 ← selected_source_c1_product c1 p L 1#usize
      let i10 ← lift (core.num.U64.wrapping_add i4 i9)
      let i15 ← selected_source_c1_product c1 p L 2#usize
      let i16 ← lift (core.num.U64.wrapping_add i10 i15)
      let i21 ← selected_source_c1_product c1 p L 3#usize
      let i22 ← lift (core.num.U64.wrapping_add i16 i21)
      let chunk ← AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk i22
      k chunk) := by
  simp only [source_c1_product_bind]


/-- The named four-product prefix returns the selected captured one-fold
chunk. This is the first-chunk component used with the exact source-prefix
continuation bridge above. -/
theorem first_c1_four_factored_chunk_success
    (c1 : Aeneas.Std.Array U32 26#usize)
    (p : AspisR614SelectedCombineBeta.query_arithmetic.BetaCoefficients)
    (L : Usize) (hL : L.val < 4)
    (hc1 : ∀ i : Fin 26, (arrayAt c1 i).val < P)
    (hp1 : ∀ i : Fin 26, ∀ r : Fin 4,
      (arrayAt (arrayAt p.c1_limbs i) r).val < P) :
    ∃ z : U64,
      (do
        let x0 ← selected_source_c1_product c1 p L 0#usize
        let x1 ← selected_source_c1_product c1 p L 1#usize
        let a01 ← lift (core.num.U64.wrapping_add x0 x1)
        let x2 ← selected_source_c1_product c1 p L 2#usize
        let a012 ← lift (core.num.U64.wrapping_add a01 x2)
        let x3 ← selected_source_c1_product c1 p L 3#usize
        let raw ← lift (core.num.U64.wrapping_add a012 x3)
        let folded ← AspisR614SelectedCombineBeta.query_arithmetic.reduce_chunk raw
        .ok folded) = .ok z ∧
      z.val < 5 * P ∧
      z.val % P =
        ((arrayAt c1 ⟨0, by norm_num⟩).val *
          (arrayAt (arrayAt p.c1_limbs ⟨0, by norm_num⟩)
            ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩).val +
         (arrayAt c1 ⟨1, by norm_num⟩).val *
          (arrayAt (arrayAt p.c1_limbs ⟨1, by norm_num⟩)
            ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩).val +
         (arrayAt c1 ⟨2, by norm_num⟩).val *
          (arrayAt (arrayAt p.c1_limbs ⟨2, by norm_num⟩)
            ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩).val +
         (arrayAt c1 ⟨3, by norm_num⟩).val *
          (arrayAt (arrayAt p.c1_limbs ⟨3, by norm_num⟩)
            ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩).val) % P := by
  let coord : Fin (4#usize).val := ⟨L.val, by
    simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩
  let i0 : Fin 26 := ⟨0, by norm_num⟩
  let i1 : Fin 26 := ⟨1, by norm_num⟩
  let i2 : Fin 26 := ⟨2, by norm_num⟩
  let i3 : Fin 26 := ⟨3, by norm_num⟩
  have hc0 := hc1 i0
  have hc1' := hc1 i1
  have hc2 := hc1 i2
  have hc3 := hc1 i3
  have hp0 := hp1 i0 ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩
  have hp1' := hp1 i1 ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩
  have hp2 := hp1 i2 ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩
  have hp3 := hp1 i3 ⟨L.val, by simpa only [show (4#usize : Usize).val = 4 from rfl] using hL⟩
  have hi0 : (0#usize : Usize).val < 26 := by simp only [UScalar.ofNatCore_val_eq]; omega
  have hi1 : (1#usize : Usize).val < 26 := by simp only [UScalar.ofNatCore_val_eq]; omega
  have hi2 : (2#usize : Usize).val < 26 := by simp only [UScalar.ofNatCore_val_eq]; omega
  have hi3 : (3#usize : Usize).val < 26 := by simp only [UScalar.ofNatCore_val_eq]; omega
  obtain ⟨x0, hx0, hv0⟩ := selected_source_c1_product_ok c1 p L 0#usize hL hi0
  obtain ⟨x1, hx1, hv1⟩ := selected_source_c1_product_ok c1 p L 1#usize hL hi1
  obtain ⟨x2, hx2, hv2⟩ := selected_source_c1_product_ok c1 p L 2#usize hL hi2
  obtain ⟨x3, hx3, hv3⟩ := selected_source_c1_product_ok c1 p L 3#usize hL hi3
  have heq0 : x0 = selectedProduct (arrayAt c1 i0) (arrayAt (arrayAt p.c1_limbs i0) coord) := by
    apply UScalar.eq_of_val_eq
    simpa only [arrayAt, coord, selectedProduct, UScalar.ofNatCore_val_eq] using hv0
  have heq1 : x1 = selectedProduct (arrayAt c1 i1) (arrayAt (arrayAt p.c1_limbs i1) coord) := by
    apply UScalar.eq_of_val_eq
    simpa only [arrayAt, coord, selectedProduct, UScalar.ofNatCore_val_eq] using hv1
  have heq2 : x2 = selectedProduct (arrayAt c1 i2) (arrayAt (arrayAt p.c1_limbs i2) coord) := by
    apply UScalar.eq_of_val_eq
    simpa only [arrayAt, coord, selectedProduct, UScalar.ofNatCore_val_eq] using hv2
  have heq3 : x3 = selectedProduct (arrayAt c1 i3) (arrayAt (arrayAt p.c1_limbs i3) coord) := by
    apply UScalar.eq_of_val_eq
    simpa only [arrayAt, coord, selectedProduct, UScalar.ofNatCore_val_eq] using hv3
  obtain ⟨z, hz, hbound, hres⟩ := selected_four_product_chunk
    (arrayAt c1 i0) (arrayAt (arrayAt p.c1_limbs i0) coord)
    (arrayAt c1 i1) (arrayAt (arrayAt p.c1_limbs i1) coord)
    (arrayAt c1 i2) (arrayAt (arrayAt p.c1_limbs i2) coord)
    (arrayAt c1 i3) (arrayAt (arrayAt p.c1_limbs i3) coord)
    hc0 hp0 hc1' hp1' hc2 hp2 hc3 hp3
  refine ⟨z, ?_, hbound, ?_⟩
  · simp only [hx0, hx1, hx2, hx3, bind_tc_ok, lift, heq0, heq1, heq2, heq3]
    exact hz
  · simpa only [arrayAt, coord, P] using hres

#print axioms fourProducts_lt_u64
#print axioms selected_index_ok
#print axioms selected_mixed_index_spec
#print axioms selected_mixed_c2_access
#print axioms selected_source_mixed_c2_access_ok
#print axioms selected_source_c1_product_ok
#print axioms source_c1_term0_eq_factored
#print axioms source_c1_product_bind
#print axioms first_c1_four_source_chunk_bind
#print axioms first_c1_four_factored_chunk_success
#print axioms source_mixed_product_bind
#print axioms source_mixed_product_literal_bind
#print axioms selected_source_mixed_product_ok
#print axioms selected_source_mixed_product_value
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
