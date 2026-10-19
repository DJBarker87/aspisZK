import AspisFormal.CircleGroupOrder
import R1ZBatchInverseAlgebraV5

set_option autoImplicit false

namespace R1ZBatchInverseSourceModelV1

variable {K : Type*} [Field K]

/-- Prefixes recorded before each multiplication in the forward pass. -/
def prefixRun : List K → K → List K
  | [], _ => []
  | x :: xs, p => p :: prefixRun xs (p * x)

theorem prefixRun_length (xs : List K) (p : K) :
    (prefixRun xs p).length = xs.length := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [prefixRun, ih]

theorem prefixRun_getD (xs : List K) (p : K) (i : Nat) (hi : i < xs.length) :
    (prefixRun xs p).getD i 1 = p * (xs.take i).prod := by
  induction xs generalizing p i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [prefixRun]
    | succ i =>
      have hlt : i < xs.length := by simp only [List.length_cons] at hi; omega
      change (prefixRun xs (p * x)).getD i 1 = p * ((x :: xs).take (i + 1)).prod
      rw [ih (p := p * x) (i := i) hlt]
      simp only [List.take_succ_cons, List.prod_cons]
      ring

/-- The mutable backward loop consumes the recorded prefix at each index, in
reverse index order, and emits writes in ascending list order. -/
def backwardsStored (xs prefixes : List K) : Nat → K → List K
  | 0, _ => []
  | n + 1, s =>
      backwardsStored xs prefixes n (s * xs.getD n 1) ++
        [s * prefixes.getD n 1]

theorem backwardsStored_eq_backwards (xs prefixes : List K) (n : Nat)
    (hn : n ≤ xs.length)
    (hp : ∀ i, i < n → prefixes.getD i 1 = (xs.take i).prod) (s : K) :
    backwardsStored xs prefixes n s = R1ZBatchInverseAlgebraV3.backwards xs n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hn' : n ≤ xs.length := by omega
    have hlt : n < xs.length := by omega
    have hpn : prefixes.getD n 1 = (xs.take n).prod := hp n (by omega)
    have hget : xs.getD n 1 = xs[n] := by simp [hlt]
    have hrec := ih hn' (fun i hi => hp i (by omega)) (s := s * xs.getD n 1)
    change (backwardsStored xs prefixes n (s * xs.getD n 1) ++
      [s * prefixes.getD n 1]) =
      (R1ZBatchInverseAlgebraV3.backwards xs n (s * xs.getD n 1) ++
      [s * (xs.take n).prod])
    rw [hrec, hpn]

theorem backwardsStored_correct (xs prefixes : List K) (n : Nat)
    (hn : n ≤ xs.length)
    (hnz : ∀ m, m ≤ n → (xs.take m).prod ≠ 0)
    (hp : ∀ i, i < n → prefixes.getD i 1 = (xs.take i).prod)
    (s : K) (hs : s = (xs.take n).prod⁻¹) :
    backwardsStored xs prefixes n s = (xs.take n).map Inv.inv := by
  rw [backwardsStored_eq_backwards xs prefixes n hn hp s]
  exact R1ZBatchInverseAlgebraV3.backwards_correct xs n hn hnz s hs

/-- At all recorded indices, the forward prefix array is the product of all
preceding denominators. -/
theorem prefixRun_getD_eq_take_prod (xs : List K) (i : Nat) (hi : i < xs.length) :
    (prefixRun xs 1).getD i 1 = (xs.take i).prod := by
  rw [prefixRun_getD xs 1 i hi]
  simp

#print axioms prefixRun_getD
#print axioms backwardsStored_correct

end R1ZBatchInverseSourceModelV1
