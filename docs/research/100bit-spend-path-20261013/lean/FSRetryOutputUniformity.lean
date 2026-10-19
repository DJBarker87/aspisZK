import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-! A finite symmetry lemma for fixed-window first-accepted samplers.
Equal-sized value fibers induce a word permutation that transposes two
accepted outputs and fixes every other output, including rejection. -/
set_option autoImplicit false
namespace FSRetryOutputUniformity

noncomputable section
open Classical

variable {W A : Type} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

def firstSome : List (Option A) → Option A
  | [] => none
  | some a :: _ => some a
  | none :: xs => firstSome xs

theorem firstSome_map (f : A → A) (xs : List (Option A)) :
    firstSome (xs.map (Option.map f)) = Option.map f (firstSome xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | none => simpa [firstSome] using ih
      | some a => rfl

def output (decode : W → Option A) (xs : Fin 16 → W) : Option A :=
  firstSome (List.ofFn fun i : Fin 16 => decode (xs i))

abbrev outputFiber (decode : W → Option A) (a : A) :=
  {xs : Fin 16 → W // output decode xs = some a}

abbrev valueFiber (decode : W → Option A) (a : A) :=
  {w : W // decode w = some a}

noncomputable def outputFiberFintype (decode : W → Option A) (a : A) :
    Fintype (outputFiber decode a) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def valueFiberFintype (decode : W → Option A) (a : A) :
    Fintype (valueFiber decode a) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def outputFiberCard (decode : W → Option A) (a : A) : Nat :=
  @Fintype.card (outputFiber decode a) (outputFiberFintype decode a)

noncomputable def valueFiberCard (decode : W → Option A) (a : A) : Nat :=
  @Fintype.card (valueFiber decode a) (valueFiberFintype decode a)

theorem output_map (decode : W → Option A) (f : A ≃ A)
    (e : Equiv.Perm W)
    (hdecode : ∀ w, decode (e w) = Option.map f (decode w))
    (xs : Fin 16 → W) :
    output decode (fun i => e (xs i)) = Option.map f (output decode xs) := by
  unfold output
  have hlist : List.ofFn (fun i : Fin 16 => decode (e (xs i))) =
      (List.ofFn fun i : Fin 16 => decode (xs i)).map (Option.map f) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hdecode (xs i)
  rw [hlist]
  exact firstSome_map f _

def valueFiberSwapFun (decode : W → Option A) (a b : A)
    (hab : a ≠ b) (e : valueFiber decode a ≃ valueFiber decode b) (w : W) : W :=
  if ha : decode w = some a then (e ⟨w, ha⟩).val
  else if hb : decode w = some b then (e.symm ⟨w, hb⟩).val
  else w

private theorem swap_involutive (a b x : A) :
    Equiv.swap a b (Equiv.swap a b x) = x := by
  by_cases hxa : x = a
  · subst x
    simp [Equiv.swap_apply_def]
  · by_cases hxb : x = b
    · subst x
      simp [Equiv.swap_apply_def]
    · simp [Equiv.swap_apply_def, hxa, hxb]

private theorem valueFiberSwapFun_involutive (decode : W → Option A)
    (a b : A) (hab : a ≠ b) (e : valueFiber decode a ≃ valueFiber decode b) :
    Function.Involutive (valueFiberSwapFun decode a b hab e) := by
  intro w
  by_cases ha : decode w = some a
  · have hb' : decode (e ⟨w, ha⟩).val = some b := (e ⟨w, ha⟩).property
    simp [valueFiberSwapFun, ha, hb', hab.symm, Equiv.symm_apply_apply]
  · by_cases hb : decode w = some b
    · have ha' : decode (e.symm ⟨w, hb⟩).val = some a :=
        (e.symm ⟨w, hb⟩).property
      simp [valueFiberSwapFun, ha, hb, ha', hab.symm, Equiv.apply_symm_apply]
    · simp [valueFiberSwapFun, ha, hb]

private theorem valueFiberSwapFun_decode (decode : W → Option A)
    (a b : A) (hab : a ≠ b) (e : valueFiber decode a ≃ valueFiber decode b) :
    ∀ w, decode (valueFiberSwapFun decode a b hab e w) =
      Option.map (Equiv.swap a b) (decode w) := by
  intro w
  by_cases ha : decode w = some a
  · have hb' : decode (e ⟨w, ha⟩).val = some b := (e ⟨w, ha⟩).property
    simp [valueFiberSwapFun, ha, hb', hab.symm]
  · by_cases hb : decode w = some b
    · have ha' : decode (e.symm ⟨w, hb⟩).val = some a :=
        (e.symm ⟨w, hb⟩).property
      simp [valueFiberSwapFun, ha, hb, ha', hab.symm]
    · cases hd : decode w with
      | none => simp [valueFiberSwapFun, ha, hb, hd]
      | some c =>
          have hca : c ≠ a := by
            intro h
            apply ha
            simp [hd, h]
          have hcb : c ≠ b := by
            intro h
            apply hb
            simp [hd, h]
          simp [valueFiberSwapFun, ha, hb, hd, hca, hcb,
            Equiv.swap_apply_def]

def valueFiberSwapPerm (decode : W → Option A) (a b : A)
    (hab : a ≠ b)
    (hcard : valueFiberCard decode a = valueFiberCard decode b) :
    Equiv.Perm W := by
  letI : Fintype (valueFiber decode a) := valueFiberFintype decode a
  letI : Fintype (valueFiber decode b) := valueFiberFintype decode b
  let e : valueFiber decode a ≃ valueFiber decode b := Fintype.equivOfCardEq hcard
  let f := valueFiberSwapFun decode a b hab e
  exact
    { toFun := f
      invFun := f
      left_inv := valueFiberSwapFun_involutive decode a b hab e
      right_inv := valueFiberSwapFun_involutive decode a b hab e }

theorem valueFiberSwapPerm_decode (decode : W → Option A) (a b : A)
    (hab : a ≠ b)
    (hcard : valueFiberCard decode a = valueFiberCard decode b) :
    ∀ w, decode (valueFiberSwapPerm decode a b hab hcard w) =
      Option.map (Equiv.swap a b) (decode w) := by
  letI : Fintype (valueFiber decode a) := valueFiberFintype decode a
  letI : Fintype (valueFiber decode b) := valueFiberFintype decode b
  let e : valueFiber decode a ≃ valueFiber decode b := Fintype.equivOfCardEq hcard
  intro w
  exact valueFiberSwapFun_decode decode a b hab e w

def act (e : Equiv.Perm W) : (Fin 16 → W) ≃ (Fin 16 → W) where
  toFun xs i := e (xs i)
  invFun xs i := e.symm (xs i)
  left_inv xs := by funext i; simp
  right_inv xs := by funext i; simp

def restrictEquiv {X : Type} (e : X ≃ X) {p q : X → Prop}
    (h : ∀ x, p x → q (e x)) (h' : ∀ x, q x → p (e.symm x)) :
    {x // p x} ≃ {x // q x} where
  toFun x := ⟨e x.1, h x.1 x.2⟩
  invFun x := ⟨e.symm x.1, h' x.1 x.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem outputFiber_card_eq (decode : W → Option A) (a b : A)
    (e : Equiv.Perm W)
    (hdecode : ∀ w, decode (e w) = Option.map (Equiv.swap a b) (decode w)) :
    outputFiberCard decode a = outputFiberCard decode b := by
  letI : Fintype (outputFiber decode a) := outputFiberFintype decode a
  letI : Fintype (outputFiber decode b) := outputFiberFintype decode b
  let E := act e
  have hforward : ∀ xs, output decode xs = some a →
      output decode (E xs) = some b := by
    intro xs hx
    have hout : output decode (E xs) =
        Option.map (Equiv.swap a b) (output decode xs) := by
      change output decode (fun i => e (xs i)) = _
      exact output_map decode (Equiv.swap a b) e hdecode xs
    rw [hout, hx]
    simp
  have hbackward : ∀ xs, output decode xs = some b →
      output decode (E.symm xs) = some a := by
    intro xs hx
    have hdecode' : ∀ w, decode (e.symm w) =
        Option.map (Equiv.swap a b) (decode w) := by
      intro w
      have hh := hdecode (e.symm w)
      have hh' : decode w = Option.map (Equiv.swap a b) (decode (e.symm w)) := by
        simpa using hh
      cases hd : decode (e.symm w) with
      | none =>
          have hw : decode w = none := by simpa [hd] using hh'
          simp [hd, hw]
      | some c =>
          have hw : decode w = some (Equiv.swap a b c) := by simpa [hd] using hh'
          rw [hw]
          simp [swap_involutive a b c]
    have hout : output decode (E.symm xs) =
        Option.map (Equiv.swap a b) (output decode xs) := by
      change output decode (fun i => e.symm (xs i)) = _
      exact output_map decode (Equiv.swap a b) e.symm hdecode' xs
    rw [hout, hx]
    simp
  let R : outputFiber decode a ≃ outputFiber decode b := {
    toFun := fun xs => ⟨E xs.1, hforward xs.1 xs.2⟩
    invFun := fun xs => ⟨E.symm xs.1, hbackward xs.1 xs.2⟩
    left_inv := by intro xs; apply Subtype.ext; simp
    right_inv := by intro xs; apply Subtype.ext; simp
  }
  simpa [outputFiberCard, outputFiberFintype] using Fintype.card_congr R

theorem outputFiber_card_eq_of_value_fiber_card (decode : W → Option A)
    (a b : A) (hab : a ≠ b)
    (hcard : valueFiberCard decode a = valueFiberCard decode b) :
    outputFiberCard decode a = outputFiberCard decode b := by
  apply outputFiber_card_eq decode a b (valueFiberSwapPerm decode a b hab hcard)
  exact valueFiberSwapPerm_decode decode a b hab hcard

end
end FSRetryOutputUniformity
