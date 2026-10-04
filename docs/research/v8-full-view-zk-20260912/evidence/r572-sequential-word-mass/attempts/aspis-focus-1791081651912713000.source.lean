import AspisV8R19.AdaptiveFirstReadLaw
import AspisV8R19.R443BoundedRejectionMass

set_option autoImplicit false
namespace AspisV8R19.R572SequentialWordMass

open MemoizedProgramLaw AdaptiveFirstReadLaw OracleResampling OracleProgramOps
open R443BoundedRejectionMass

variable {p : Nat}

noncomputable section

def scan : (n : Nat) → Nat → Program Nat (Option (Fin p)) (Option (Fin p) × Nat)
  | 0, cursor => .done (none, cursor)
  | n + 1, cursor => .ask cursor (fun answer =>
      match answer with
      | none => scan n (cursor + 1)
      | some a => .done (some a, cursor + 1))

def prependResult (a : Fin p) (r : Option (List (Fin p)) × Nat) :
    Option (List (Fin p)) × Nat :=
  match r.1 with
  | none => (none, r.2)
  | some xs => (some (a :: xs), r.2)

def limbs : (budget count : Nat) → Nat → Program Nat (Option (Fin p)) (Option (List (Fin p)) × Nat)
  | _, 0, cursor => .done (some [], cursor)
  | budget, count + 1, cursor => bind (scan budget cursor) (fun first =>
      match first.1 with
      | none => .done (none, first.2)
      | some a => bind (limbs budget count first.2) (fun tail =>
          .done (prependResult a tail)))

def observedList (target : List (Fin p)) : View Nat (Option (Fin p))
    (Option (List (Fin p)) × Nat) → ℚ :=
  fun view => if view.2.1 = some target then 1 else 0

noncomputable def scanMass (n cursor : Nat) (f : Option (Fin p) → ℚ) : ℚ :=
  independentMean (scan n cursor) (fun view => f view.2.1)

theorem scanMass_cursor (n : Nat) (cursor₁ cursor₂ : Nat)
    (f : Option (Fin p) → ℚ) : scanMass n cursor₁ f = scanMass n cursor₂ f := by
  induction n generalizing cursor₁ cursor₂ with
  | zero => rfl
  | succ n ih =>
      simp only [scanMass, scan, independentMean]
      apply mean_congr
      intro answer
      cases answer with
      | none => simpa [scanMass, scan] using ih _ _
      | some a => rfl

theorem scanMass_step (n cursor : Nat) (f : Option (Fin p) → ℚ) :
    scanMass (n + 1) cursor f =
      (scanMass n cursor f + ∑ a : Fin p, f (some a)) / (p + 1 : ℚ) := by
  change mean (fun answer : Option (Fin p) =>
    independentMean
      (match answer with
       | none => scan n (cursor + 1)
       | some a => .done (some a, cursor + 1))
      (fun view => f view.2.1)) = _
  rw [mean_option]
  congr 1
  · simpa [scanMass] using scanMass_cursor n (cursor + 1) cursor f
  · apply Finset.sum_congr rfl
    intro a ha
    rfl

theorem scanMass_value (n cursor : Nat) (a : Fin p) (hp : 0 < p) :
    scanMass n cursor (fun x => if x = some a then 1 else 0) = valueMass p n a := by
  induction n with
  | zero => simp [scanMass, scan, independentMean, valueMass, run, mean_const]
  | succ n ih =>
      rw [scanMass_step, ih, value_mass]
      simp only [Option.some.injEq]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      change ((1 - (1 / (p + 1 : ℚ)) ^ n) / p + 1) / (p + 1 : ℚ) = _
      rw [value_mass, pow_succ]
      field_simp
      ring

theorem scanMass_scaled (n cursor : Nat) (a : Fin p) (c : ℚ) :
    scanMass n cursor (fun x => if x = some a then c else 0) =
      c * scanMass n cursor (fun x => if x = some a then 1 else 0) := by
  induction n with
  | zero => simp [scanMass, scan, independentMean, mean_const]
  | succ n ih =>
      rw [scanMass_step, scanMass_step, ih]
      simp only [Option.some.injEq]
      rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      ring

theorem prepend_mass (budget count cursor : Nat) (a head : Fin p)
    (tailTarget : List (Fin p)) :
    independentMean
      (bind (limbs budget count cursor) (fun tail => .done (prependResult a tail)))
      (observedList (head :: tailTarget)) =
      if a = head then
        independentMean (limbs budget count cursor) (observedList tailTarget)
      else 0 := by
  rw [independentMean_bind]
  apply mean_congr
  intro first
  simp [independentMean, observedList, prependResult]

theorem independentMean_congr {I A O : Type} [Fintype A]
    (program : Program I A O) {f g : View I A O → ℚ}
    (h : ∀ view, f view = g view) :
    independentMean program f = independentMean program g := by
  induction program with
  | done output => exact h ([], output)
  | ask address next ih =>
      simp only [independentMean]
      apply mean_congr
      intro answer
      exact ih answer (fun view => h ((address, answer) :: view.1, view.2))

theorem limbs_exact_mass (hp : 0 < p) (budget count cursor : Nat)
    (target : Fin count → Fin p) :
    independentMean (limbs budget count cursor)
      (observedList (List.ofFn target)) =
      ((1 - (1 / (p + 1 : ℚ)) ^ budget) / p) ^ count := by
  induction count generalizing cursor with
  | zero =>
      simp [limbs, independentMean, observedList, mean_const]
  | succ count ih =>
      -- A successful first scan fixes the head. Its tail continuation has
      -- the induction-hypothesis mass for every cursor, including the one
      -- reached after the scan; failed scans preserve their advanced cursor.
      have tail : Fin count → Fin p := fun i => target i.succ
      have htarget : List.ofFn target = target 0 :: List.ofFn tail := by
        rw [List.ofFn_succ]
      rw [htarget]
      change independentMean
        (bind (scan budget cursor) (fun first =>
          match first.1 with
          | none => .done (none, first.2)
          | some a => bind (limbs budget count first.2)
              (fun rest => .done (prependResult a rest))))
        (observedList (target 0 :: List.ofFn tail)) = _
      rw [independentMean_bind]
      let tailMass := ((1 - (1 / (p + 1 : ℚ)) ^ budget) / p) ^ count
      have hcontinuation : ∀ first : View Nat (Option (Fin p))
          (Option (Fin p) × Nat),
          independentMean
            (match first.2.1 with
             | none => .done (none, first.2.2)
             | some a => bind (limbs budget count first.2.2)
                 (fun rest => .done (prependResult a rest)))
            (fun second => observedList (target 0 :: List.ofFn tail)
              (first.1 ++ second.1, second.2)) =
          if first.2.1 = some (target 0) then tailMass else 0 := by
        intro first
        cases hout : first.2.1 with
        | none => simp [hout, independentMean, observedList]
        | some a =>
            rw [prepend_mass]
            by_cases ha : a = target 0
            · subst a
              have hi := ih first.2.2 tail
              simpa [tailMass, observedList] using hi
            · simp [ha]
      have hscan :
          independentMean (scan budget cursor)
            (fun first => if first.2.1 = some (target 0) then tailMass else 0) =
          tailMass * scanMass budget cursor
            (fun x => if x = some (target 0) then 1 else 0) := by
        change scanMass budget cursor
          (fun x => if x = some (target 0) then tailMass else 0) = _
        rw [scanMass_scaled]
      have hc := scanMass_value budget cursor (target 0) hp
      rw [independentMean_congr (scan budget cursor) hcontinuation, hscan, hc, ih]
      dsimp [tailMass]
      ring

#print axioms scanMass_cursor
#print axioms scanMass_step
#print axioms scanMass_value
#print axioms limbs_exact_mass
end AspisV8R19.R572SequentialWordMass
end
