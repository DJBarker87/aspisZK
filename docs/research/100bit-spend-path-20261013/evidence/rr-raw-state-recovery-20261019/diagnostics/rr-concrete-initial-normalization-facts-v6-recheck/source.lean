import RRConcreteStatePolynomialView
import RRVectorRowNonzeroV5
import RRFiniteCoeffScannerV9
import RRInitialFullRowsScanFacts
import RRInitialNonzeroRowBridge
import RRInitialDroppedModelBridge
import RRChildNormalization
import RRPrefixCollector

set_option autoImplicit false
open Polynomial
namespace AspisR1.RRConcreteInitialNormalizationFromFacts

open RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState
open AspisR1.RRConcreteStatePolynomialView
open RRVectorNormalizedRows
open AspisR1.RRInitialNonzeroRowBridge
open AspisR1.RRInitialDroppedModelBridge
open RRActualBivariateTaylorBridge RRFiniteCoeffScannerV9 RRRootDescent RRVectorRowScannerBridge

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def rowIsZero (row : List K) : Bool := rowNonzeroFull row == false

def initialNormalizeRaw (s : RawState K) : Option (RawState K) :=
  match firstNonzeroFullRows (s.rows.take (s.maxX + 1)) with
  | none => none
  | some (v, _) => some ⟨s.rows.drop v, s.maxX - v⟩

private theorem all_rows_zero_at
    (xs : List (List K)) (hall : xs.all rowIsZero = true)
    (i : Nat) (hi : i < xs.length) : rowNonzeroFull xs[i] = false := by
  have hmem : xs[i] ∈ xs := List.getElem_mem hi
  have hz := (List.all_eq_true.mp hall) _ hmem
  change (rowNonzeroFull xs[i] == false) = true at hz
  cases hb : rowNonzeroFull xs[i] <;> simp [hb] at hz ⊢

private theorem inputPolynomial_drop
    (gs : List (List K)) (v i : Nat) :
    inputPolynomial (gs.drop v) i = inputPolynomial gs (v+i) := by
  simp [inputPolynomial, vectorAt, List.getElem?_drop, Nat.add_comm]

private theorem initial_strip_low_coefficients
    (s : RawState K) (v : Nat) (hv : v ≤ s.maxX)
    (hlow : ∀ i < v, inputPolynomial s.rows i = 0) :
    ∀ j n, n < v → ((model s).coeff j).coeff n = 0 := by
  intro j n hn
  have hslice : xCoeffSlice (model s) n = 0 := by
    have hread := parent_inner_slice (inputPolynomial s.rows) s.maxX n
    have hnM : n ≤ s.maxX := by omega
    simpa only [model, actualParent, hnM, ↓reduceIte, hlow n hn] using hread
  have hc := congrArg (fun p : K[X] => p.coeff j) hslice
  simpa [xCoeffSlice_coeff] using hc

theorem initial_scan_and_normalize
    (ell : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) :
    ∃ v row childRaw,
      firstNonzeroFullRows (s.rows.take (s.maxX+1)) = some (v,row) ∧
      initialNormalizeRaw s = some childRaw ∧
      childRaw = ⟨s.rows.drop v, s.maxX-v⟩ ∧
      Valid ell childRaw ∧
      model s = C ((X : K[X])^v) * model childRaw ∧
      (∀ f : K[X], (model childRaw).eval f = 0 ↔ (model s).eval f = 0) := by
  obtain ⟨i, hi, hinput⟩ := exists_nonzero_initial_row s hQ
  have hirows : i < s.rows.length := by
    by_contra hnot
    have hget : s.rows[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    have hvec : vectorAt s.rows i = [] := by simp [vectorAt, hget]
    have hz : inputPolynomial s.rows i = 0 := by
      rw [inputPolynomial, hvec]
      exact RRPrefixCollector.toPolynomial_nil
    exact hinput hz
  let xs := s.rows.take (s.maxX+1)
  have hidx : i < xs.length := by
    simp [xs, List.length_take]
    omega
  have hoptTakeI : xs[i]? = s.rows[i]? := by
    simpa [xs] using (List.getElem?_take_of_lt (l := s.rows) (i := i)
      (j := s.maxX+1) (by omega))
  have hvecI : vectorAt s.rows i = xs[i] := by
    dsimp [vectorAt]
    rw [← hoptTakeI]
    simp [List.getElem?_eq_getElem hidx]
  have hrow : rowNonzeroFull xs[i] = true := by
    have hb := (rowNonzero_iff_toPolynomial_ne (vectorAt s.rows i)).2 hinput
    simpa [hvecI] using hb
  cases hscan : firstNonzeroFullRows xs with
  | none =>
      have hall : xs.all rowIsZero = true :=
        (RRInitialFullRowsScanFacts.firstNonzeroFullRows_none_iff_allZero xs).mp hscan
      have hzero := all_rows_zero_at xs hall i hidx
      exact (Bool.false_ne_true (hzero.symm.trans hrow)).elim
  | some pair =>
      rcases pair with ⟨v,row⟩
      have hscan' : firstNonzeroFullRows xs = some (v,row) := hscan
      obtain ⟨pre,post,hxs,hlen,hprezero,hrownz⟩ :=
        RRInitialFullRowsScanFacts.firstNonzeroFullRows_some_decompose xs v row hscan'
      have hprezero' : ∀ x ∈ pre, rowNonzeroFull x = false := by
        intro x hx
        have hz := (List.all_eq_true.mp hprezero) x hx
        change (rowNonzeroFull x == false) = true at hz
        cases hb : rowNonzeroFull x <;> simp [hb] at hz ⊢
      have hvlt : v < xs.length := by
        rw [hxs]
        simp [hlen]
      have hv : v ≤ s.maxX := by
        have hlenTake : xs.length ≤ s.maxX+1 := by
          simp [xs, List.length_take]
        omega
      have hlow : ∀ j < v, inputPolynomial s.rows j = 0 := by
        intro j hj
        have hjpre : j < pre.length := by omega
        have hzeroPre := hprezero' pre[j] (List.getElem_mem hjpre)
        have hxsPreOpt : xs[j]? = pre[j]? := by
          have hcong := congrArg (fun ys : List (List K) => ys[j]?) hxs
          simpa [List.getElem?_append, hjpre] using hcong
        have hjxs : j < xs.length := by
          rw [hxs]
          simp only [List.length_append, List.length_cons]
          omega
        have hxsPre : xs[j] = pre[j] := by
          have htmp := hxsPreOpt
          rw [List.getElem?_eq_getElem hjxs, List.getElem?_eq_getElem hjpre] at htmp
          exact Option.some.inj htmp
        have hzeroXs : rowNonzeroFull xs[j] = false := by simpa [hxsPre] using hzeroPre
        have hoptTake : xs[j]? = s.rows[j]? := by
          simpa [xs] using (List.getElem?_take_of_lt (l := s.rows) (i := j)
            (j := s.maxX+1) (by omega))
        have hrowOrig : vectorAt s.rows j = xs[j] := by
          dsimp [vectorAt]
          rw [← hoptTake]
          simp [List.getElem?_eq_getElem hjxs]
        have hzeroVector : rowNonzeroFull (vectorAt s.rows j) = false := by
          simpa [hrowOrig] using hzeroXs
        by_contra hne
        have htrue := (rowNonzero_iff_toPolynomial_ne (vectorAt s.rows j)).2 hne
        rw [hzeroVector] at htrue
        cases htrue
      have hscanRowOpt : xs[v]? = some row := by
        have hcong := congrArg (fun ys : List (List K) => ys[v]?) hxs
        simpa [List.getElem?_append, hlen] using hcong
      have hoptTakeV : xs[v]? = s.rows[v]? := by
        simpa [xs] using (List.getElem?_take_of_lt (l := s.rows) (i := v)
          (j := s.maxX+1) (by omega))
      have hrowOrig : rowNonzeroFull (vectorAt s.rows v) = true := by
        have hrowOpt : s.rows[v]? = some row := hoptTakeV.symm.trans hscanRowOpt
        simpa [vectorAt, hrowOpt] using hrownz
      have hfirst : inputPolynomial (s.rows.drop v) 0 ≠ 0 := by
        have hne : inputPolynomial s.rows v ≠ 0 :=
          (rowNonzero_iff_toPolynomial_ne (vectorAt s.rows v)).1 hrowOrig
        simpa [inputPolynomial_drop, Nat.zero_add] using hne
      have hvalid : Valid ell ⟨s.rows.drop v, s.maxX-v⟩ := by
        change inputPolynomial (s.rows.drop v) 0 ≠ 0 ∧
          ∀ j ≤ s.maxX-v, (inputPolynomial (s.rows.drop v) j).natDegree ≤ ell
        constructor
        · exact hfirst
        · intro j hj
          rw [inputPolynomial_drop]
          apply hdegree
          omega
      have hlowc := initial_strip_low_coefficients s v hv hlow
      have hmodeldrop : model ⟨s.rows.drop v, s.maxX-v⟩ = stripInnerPower (model s) v :=
        dropped_model_eq_stripInnerPower s v hv hlow
      let childRaw : RawState K := ⟨s.rows.drop v, s.maxX-v⟩
      have hmodeldropChild : model childRaw = stripInnerPower (model s) v := by
        simpa [childRaw] using hmodeldrop
      have hfactor : model s = C ((X : K[X])^v) * model childRaw := by
        rw [hmodeldropChild]
        exact stripInnerPower_factor (model s) v hlowc
      have hroots : ∀ f : K[X], (model childRaw).eval f = 0 ↔ (model s).eval f = 0 := by
        intro f
        have heval := congrArg (fun p : (K[X])[X] => p.eval f) hfactor
        simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
        constructor
        · intro hf
          rw [heval, hf, mul_zero]
        · intro hq
          have hmul : ((X : K[X])^v) * (model childRaw).eval f = 0 := heval.symm.trans hq
          have hpow : ((X : K[X])^v) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
          exact (mul_eq_zero.mp hmul).resolve_left hpow
      have hraw : childRaw = ⟨s.rows.drop v, s.maxX-v⟩ := rfl
      have hscanOrig : firstNonzeroFullRows (s.rows.take (s.maxX+1)) = some (v,row) := by
        simpa [xs] using hscan'
      have hnormalize : initialNormalizeRaw s = some childRaw := by
        simp [initialNormalizeRaw, hscanOrig, hraw]
      exact ⟨v,row,childRaw,rfl,hnormalize,hraw,hvalid,hfactor,hroots⟩

#print axioms initial_scan_and_normalize
end AspisR1.RRConcreteInitialNormalizationFromFacts
