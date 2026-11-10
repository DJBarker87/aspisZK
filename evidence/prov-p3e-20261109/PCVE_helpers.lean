section PCVEhelpers
open Aeneas Aeneas.Std Result ControlFlow Error
open Lean.Order

namespace PRVH

/-- checked `x >>> i` (Usize by Usize) equals the wrapping shift by `i as u32` whenever the amount is below 32 (so below `Usize.numBits`, which is 32 or 64). -/
theorem usize_shr_usize (x i : Std.Usize) (h : i.val < 32) :
    (x >>> i : Result Std.Usize) = ok (Std.Usize.wrapping_shr x (UScalar.cast .U32 i)) := by
  show UScalar.shiftRight_UScalar x i = _
  unfold UScalar.shiftRight_UScalar
  have hc : (UScalar.cast .U32 i).val = i.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
  rcases System.Platform.numBits_eq with hb | hb
  · simp [UScalar.shiftRight, Std.Usize.wrapping_shr, UScalar.wrapping_shr, UScalarTy.numBits, hc, hb]
    rw [if_pos h, Nat.mod_eq_of_lt h]
  · simp [UScalar.shiftRight, Std.Usize.wrapping_shr, UScalar.wrapping_shr, UScalarTy.numBits, hc, hb]
    rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

/-- checked `x <<< i` (Usize by Usize) equals the wrapping shift by `i as u32` whenever the amount is below 32. -/
theorem usize_shl_usize (x i : Std.Usize) (h : i.val < 32) :
    (x <<< i : Result Std.Usize) = ok (Std.Usize.wrapping_shl x (UScalar.cast .U32 i)) := by
  show UScalar.shiftLeft_UScalar x i = _
  unfold UScalar.shiftLeft_UScalar
  have hc : (UScalar.cast .U32 i).val = i.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
  rcases System.Platform.numBits_eq with hb | hb
  · simp [UScalar.shiftLeft, Std.Usize.wrapping_shl, UScalar.wrapping_shl, UScalarTy.numBits, hc, hb]
    rw [if_pos h, Nat.mod_eq_of_lt h]
  · simp [UScalar.shiftLeft, Std.Usize.wrapping_shl, UScalar.wrapping_shl, UScalarTy.numBits, hc, hb]
    rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

end PRVH
#print axioms PRVH.usize_shr_usize
#print axioms PRVH.usize_shl_usize

namespace PRVC

/-- one step of the Aeneas `loop` functional -/
def bs {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) : Result β :=
  match body x with
  | ok r => match r with
    | ControlFlow.cont x' => h x'
    | ControlFlow.done y => ok y
  | fail e => fail e
  | div => div

theorem bs_mono {α β : Type _} (body : α → Result (ControlFlow α β)) (h1 h2 : α → Result β)
    (hle : ∀ x, h1 x ⊑ h2 x) (x : α) : bs body h1 x ⊑ bs body h2 x := by
  unfold bs
  cases body x with
  | ok r => cases r with
    | cont x' => exact hle x'
    | done y => exact PartialOrder.rel_refl
  | fail e => exact PartialOrder.rel_refl
  | div => exact PartialOrder.rel_refl

theorem loop_unfold {α β : Type _} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = bs body (loop body) x := by
  rw [loop]; rfl
#print axioms loop_unfold


theorem adm_le {β : Type _} (g : Result β) : admissible (fun r : Result β => r ⊑ g) :=
  admissible_flatOrder (b := (div : Result β)) (fun r : Result β => r ⊑ g) FlatOrder.rel.bot

theorem loop_le {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hg : ∀ x, bs body g x ⊑ g x) : ∀ x, loop body x ⊑ g x := by
  refine loop.fixpoint_induct body (fun f => ∀ x, f x ⊑ g x) ?_ ?_
  · exact admissible_pi_apply (fun x (r : Result β) => r ⊑ g x) (fun x => adm_le (g x))
  · intro f hf x
    exact PartialOrder.rel_trans (bs_mono body f g hf x) (hg x)

theorem loop_eq {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hfix : ∀ x, g x = bs body g x)
    (hmin : ∀ h : α → Result β, (∀ x, bs body h x ⊑ h x) → ∀ x, g x ⊑ h x) :
    ∀ x, loop body x = g x := by
  intro x
  have h1 : loop body x ⊑ g x := loop_le body g (fun y => by rw [← hfix y]) x
  have h2 : g x ⊑ loop body x :=
    hmin (loop body) (fun y => by rw [← loop_unfold]) x
  exact PartialOrder.rel_antisymm h1 h2
#print axioms loop_eq


/-- curried-pair admissibility helpers for `X.fixpoint_induct` motives -/
theorem adm_le1 {α β : Type _} (h : α → Result β) :
    admissible (fun f : α → Result β => ∀ a, f a ⊑ h a) :=
  admissible_pi_apply (fun a (r : Result β) => r ⊑ h a) (fun a => adm_le (h a))

theorem adm_le2 {α₁ α₂ β : Type _} (h : α₁ → α₂ → Result β) :
    admissible (fun f : α₁ → α₂ → Result β => ∀ a b, f a b ⊑ h a b) :=
  admissible_pi_apply (fun a (g : α₂ → Result β) => ∀ b, g b ⊑ h a b)
    (fun a => adm_le1 (h a))

theorem adm_le3 {α₁ α₂ α₃ β : Type _} (h : α₁ → α₂ → α₃ → Result β) :
    admissible (fun f : α₁ → α₂ → α₃ → Result β => ∀ a b c, f a b c ⊑ h a b c) :=
  admissible_pi_apply (fun a (g : α₂ → α₃ → Result β) => ∀ b c, g b c ⊑ h a b c)
    (fun a => adm_le2 (h a))

theorem adm_le4 {α₁ α₂ α₃ α₄ β : Type _} (h : α₁ → α₂ → α₃ → α₄ → Result β) :
    admissible (fun f : α₁ → α₂ → α₃ → α₄ → Result β => ∀ a b c d, f a b c d ⊑ h a b c d) :=
  admissible_pi_apply (fun a (g : α₂ → α₃ → α₄ → Result β) => ∀ b c d, g b c d ⊑ h a b c d)
    (fun a => adm_le3 (h a))


theorem bs_bind {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) :
    bs body h x = Bind.bind (body x) (fun r => match r with
      | ControlFlow.cont x' => h x'
      | ControlFlow.done y => ok y) := by
  unfold bs
  cases body x with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl

theorem ite_bind {α β : Type _} (c : Prop) [Decidable c] (a b : Result α) (K : α → Result β) :
    Bind.bind (if c then a else b) K = if c then Bind.bind a K else Bind.bind b K := by
  by_cases hc : c <;> simp [hc]

theorem dite_bind {α β : Type _} (c : Prop) [Decidable c] (a : c → Result α) (b : ¬c → Result α)
    (K : α → Result β) :
    Bind.bind (dite c a b) K = dite c (fun h => Bind.bind (a h) K) (fun h => Bind.bind (b h) K) := by
  by_cases hc : c <;> simp [hc]


theorem bind_congr {α β : Type _} {m : Result α} {f f' : α → Result β} (h : ∀ a, f a = f' a) :
    Bind.bind m f = Bind.bind m f' := by
  have : f = f' := funext h
  rw [this]

theorem ite_congr' {α : Type _} (c : Prop) [Decidable c] {a a' b b' : Result α}
    (h1 : a = a') (h2 : b = b') : (if c then a else b) = (if c then a' else b') := by
  rw [h1, h2]

theorem dite_congr' {α : Type _} (c : Prop) [Decidable c] {a a' : c → Result α} {b b' : ¬c → Result α}
    (h1 : ∀ h, a h = a' h) (h2 : ∀ h, b h = b' h) : dite c a b = dite c a' b' := by
  have e1 : a = a' := funext h1
  have e2 : b = b' := funext h2
  rw [e1, e2]


theorem rel_of_eq' {γ : Type _} [Lean.Order.PartialOrder γ] {a b : γ} (h : a = b) : a ⊑ b := by
  rw [h]

theorem loop_eq_of_le {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hpre : ∀ x, bs body g x ⊑ g x) (hge : ∀ x, g x ⊑ loop body x) :
    ∀ x, loop body x = g x :=
  fun x => PartialOrder.rel_antisymm (loop_le body g hpre x) (hge x)
#print axioms loop_eq_of_le

theorem adm_le5 {α1 α2 α3 α4 α5 β : Type _} (h : α1 → α2 → α3 → α4 → α5 → Result β) :
    admissible (fun f : α1 → α2 → α3 → α4 → α5 → Result β => ∀ x1 x2 x3 x4 x5, f x1 x2 x3 x4 x5 ⊑ h x1 x2 x3 x4 x5) :=
  admissible_pi_apply (fun x1 (g : α2 → α3 → α4 → α5 → Result β) => ∀ x2 x3 x4 x5, g x2 x3 x4 x5 ⊑ h x1 x2 x3 x4 x5)
    (fun a => adm_le4 (h a))

theorem adm_le6 {α1 α2 α3 α4 α5 α6 β : Type _} (h : α1 → α2 → α3 → α4 → α5 → α6 → Result β) :
    admissible (fun f : α1 → α2 → α3 → α4 → α5 → α6 → Result β => ∀ x1 x2 x3 x4 x5 x6, f x1 x2 x3 x4 x5 x6 ⊑ h x1 x2 x3 x4 x5 x6) :=
  admissible_pi_apply (fun x1 (g : α2 → α3 → α4 → α5 → α6 → Result β) => ∀ x2 x3 x4 x5 x6, g x2 x3 x4 x5 x6 ⊑ h x1 x2 x3 x4 x5 x6)
    (fun a => adm_le5 (h a))

theorem uncurry_proj {α β γ : Type _} (f : α → β → γ) (p : α × β) :
    Aeneas.Std.uncurry f p = f p.1 p.2 := by cases p; rfl

/-- normalise both sides, one side at a time (a whole-goal `simp` can refuse on dependent numerals) -/
macro "prv_norm" : tactic => `(tactic| (
  try (conv_lhs => simp only [bind_assoc_eq, ite_bind, dite_bind, bind_tc_ok, Aeneas.Std.bind_ok, Aeneas.Std.uncurry_apply_pair, uncurry_proj])
  try (conv_rhs => simp only [bind_assoc_eq, ite_bind, dite_bind, bind_tc_ok, Aeneas.Std.bind_ok, Aeneas.Std.uncurry_apply_pair, uncurry_proj])))

/-- push the loop continuation inward and match the two do-block shapes -/
macro "prv_peel" : tactic => `(tactic| (
  prv_norm
  repeat (first
    | with_reducible rfl
    | (apply PRVC.bind_congr; intro a; try (obtain ⟨_, _⟩ := a); prv_norm)
    | (apply PRVC.ite_congr'; prv_norm)
    | (apply PRVC.dite_congr' <;> intro h)
    | (split <;> prv_norm))))

end PRVC


namespace PRVH

/-- A domain-restricted loop comparison: if two loop bodies agree on an invariant domain that the first body preserves, the loops agree on that domain. -/
theorem loop_le_dom {α β : Type _} (F G : α → Result (ControlFlow α β)) (Inv : α → Prop)
    (hFG : ∀ x, Inv x → F x = G x)
    (hpres : ∀ x x', Inv x → F x = ok (ControlFlow.cont x') → Inv x') :
    ∀ x, Inv x → loop F x ⊑ loop G x := by
  have adm : admissible (fun f : α → Result β => ∀ x, Inv x → f x ⊑ loop G x) := by
    apply admissible_pi_apply (fun x (r : Result β) => Inv x → r ⊑ loop G x)
    intro x
    by_cases h : Inv x
    · simpa [h] using PRVC.adm_le (loop G x)
    · simp [h]
      exact fun c _ _ => trivial
  refine loop.fixpoint_induct F (fun f => ∀ x, Inv x → f x ⊑ loop G x) adm ?_
  intro f hf x hx
  rw [PRVC.loop_unfold G x]
  unfold PRVC.bs
  rw [← hFG x hx]
  dsimp only
  cases hFx : F x with
  | ok r =>
    cases r with
    | cont x' => exact hf x' (hpres x x' hx hFx)
    | done y => exact PartialOrder.rel_refl
  | fail e => exact PartialOrder.rel_refl
  | div => exact PartialOrder.rel_refl

theorem loop_eq_dom {α β : Type _} (F G : α → Result (ControlFlow α β)) (Inv : α → Prop)
    (hFG : ∀ x, Inv x → F x = G x)
    (hpres : ∀ x x', Inv x → F x = ok (ControlFlow.cont x') → Inv x') :
    ∀ x, Inv x → loop F x = loop G x := by
  intro x hx
  apply PartialOrder.rel_antisymm
  · exact loop_le_dom F G Inv hFG hpres x hx
  · refine loop_le_dom G F Inv (fun y hy => (hFG y hy).symm) ?_ x hx
    intro y y' hy hG
    exact hpres y y' hy (by rw [hFG y hy]; exact hG)

/-- `Range::next` keeps the end of the range. -/
theorem range_next_end {A : Type} (S : core.iter.range.Step A) (r r1 : core.ops.range.Range A)
    (o : Option A) (h : core.iter.range.IteratorRange.next S r = ok (o, r1)) :
    r1.«end» = r.«end» := by
  unfold core.iter.range.IteratorRange.next at h
  cases hlt : S.partialOrdInst.lt r.start r.«end» with
  | fail e => simp [hlt] at h
  | div => simp [hlt] at h
  | ok c =>
    cases c with
    | false => simp [hlt] at h; rw [← h.2]
    | true =>
      cases hcl : S.cloneInst.clone r.start with
      | fail e => simp [hlt, hcl] at h
      | div => simp [hlt, hcl] at h
      | ok r' =>
        cases hfc : S.forward_checked r' 1#usize with
        | fail e => simp [hlt, hcl, hfc] at h
        | div => simp [hlt, hcl, hfc] at h
        | ok n =>
          cases n with
          | none => simp [hlt, hcl, hfc] at h
          | some n => simp [hlt, hcl, hfc] at h; rw [← h.2]

end PRVH
#print axioms PRVH.loop_le_dom
#print axioms PRVH.loop_eq_dom
#print axioms PRVH.range_next_end
end PCVEhelpers
