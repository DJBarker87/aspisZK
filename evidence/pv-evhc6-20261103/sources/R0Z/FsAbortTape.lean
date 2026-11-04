import R0Z.FsAbortBounds

/-! ZF1a/b on R1 (DESIGN-ZF1-COUPLINGS-R1 §3.1, §5.2): two generic facts used
by the tape factor of the real coupling.

* `mean_decodeOrSpare`: a rejection decoder `dec : B → Option T` whose fibres
  over `some t` all have the same size, completed by an independent uniform
  spare on `none`, is measure-preserving onto uniform `T`. This is the
  `meanM` half of the tape coupling once the R1 mask sampler's equal-fibre
  property is given (HYP; by symmetry of the accepted word values).
* `mass_fst`: an event of the first factor of a product has its own mass
  (used to read the tape factor off the coupling space).
The per-limb exhaustion mass `(2/2^32)^16` of §5.2 is not formalised here
(HYP H-exh). -/
set_option autoImplicit false
noncomputable section
namespace R0Z.FsAbortTape
open R0Z.FsAbortBounds
attribute [local instance] Classical.propDecidable

/-! ### Rejection with a uniform spare -/

theorem sum_fibres {B T : Type} [Fintype B] [Fintype T] (dec : B → Option T) (g : Option T → ℚ) :
    ∑ b, g (dec b) =
      ((Finset.univ.filter (fun b => dec b = none)).card : ℚ) * g none +
        ∑ t, ((Finset.univ.filter (fun b => dec b = some t)).card : ℚ) * g (some t) := by
  have hc : ∀ o : Option T, ∑ b ∈ Finset.univ.filter (fun b => dec b = o), g (dec b) =
      ((Finset.univ.filter (fun b => dec b = o)).card : ℚ) * g o := by
    intro o
    calc ∑ b ∈ Finset.univ.filter (fun b => dec b = o), g (dec b)
        = ∑ b ∈ Finset.univ.filter (fun b => dec b = o), g o :=
          Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2])
      _ = ((Finset.univ.filter (fun b => dec b = o)).card : ℚ) * g o := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_fiberwise Finset.univ dec (fun b => g (dec b)), Fintype.sum_option, hc none]
  congr 1
  exact Finset.sum_congr rfl (fun t _ => hc (some t))

theorem mean_decodeOrSpare {B T : Type} [Fintype B] [Fintype T] [Nonempty B] [Nonempty T]
    (dec : B → Option T) (c : ℕ)
    (hfib : ∀ t, (Finset.univ.filter (fun b => dec b = some t)).card = c) (f : T → ℚ) :
    mean (fun p : B × T => f ((dec p.1).getD p.2)) = mean f := by
  set n0 : ℚ := ((Finset.univ.filter (fun b => dec b = none)).card : ℚ) with hn0
  set F : ℚ := ∑ t, f t with hF
  have hT : (Fintype.card T : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let w : Option T → ℚ := fun o => match o with
    | none => F
    | some t => (Fintype.card T : ℚ) * f t
  have hinner : ∀ b, ∑ t', f ((dec b).getD t') = w (dec b) := by
    intro b
    cases hb : dec b with
    | none => simp [w, hF]
    | some t => simp [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnum : ∑ p : B × T, f ((dec p.1).getD p.2) =
      (n0 + c * Fintype.card T) * F := by
    rw [Fintype.sum_prod_type]
    simp only [hinner]
    rw [sum_fibres dec w]
    simp only [hfib, w]
    rw [← hn0, ← Finset.mul_sum, ← Finset.mul_sum, ← hF]
    ring
  have hcard : (Fintype.card B : ℚ) = n0 + c * Fintype.card T := by
    have h1 := sum_fibres dec (fun _ => (1 : ℚ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfib] at h1
    rw [← hn0] at h1
    rw [h1]
    ring
  unfold mean
  rw [hnum, Fintype.card_prod, Nat.cast_mul, ← hcard, hF]
  exact mul_div_mul_left _ _ hB

/-! ### Product marginal -/

/-- An event of the first factor of a product has its own mass. -/
theorem mass_fst {R X : Type} [Fintype R] [Fintype X] [Nonempty X] (Q : R → Prop) :
    mass (fun t : R × X => Q t.1) = mass Q := by
  rw [mass_prod]
  show mean _ = mean _
  congr 1
  funext r
  by_cases hq : Q r
  · rw [if_pos hq, mass_congr (fun x : X => Q (r, x).1) (fun _ => True)
      (fun _ => ⟨fun _ => trivial, fun _ => hq⟩)]
    exact mass_true
  · rw [if_neg hq, mass_congr (fun x : X => Q (r, x).1) (fun _ => False)
      (fun _ => ⟨fun h => hq h, fun h => h.elim⟩)]
    exact mass_false

#print axioms sum_fibres
#print axioms mean_decodeOrSpare
#print axioms mass_fst
end R0Z.FsAbortTape
