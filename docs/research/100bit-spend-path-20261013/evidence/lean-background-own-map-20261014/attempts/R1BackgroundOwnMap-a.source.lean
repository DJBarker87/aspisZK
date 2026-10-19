import R0C.V3.BS

/-! A result-type map for background samplers. -/
set_option autoImplicit false
namespace AspisR1.BackgroundOwnMap

open R0C.V3
open FS
open AspisV8PairedCommitment
open AspisV8R19.OracleResampling

section
variable {I A X Y : Type}

def map (f : X → Y) : BS I A X → BS I A Y
  | .done x => .done (f x)
  | .ask i k => .ask i (fun a => map f (k a))
  | .spawn c nxt => .spawn c (map f nxt)

theorem pushSpawns_map (f : X → Y) :
    ∀ (own : BS I A X) (pend : List (I × Option A)),
      pushSpawns (map f own) pend =
        (map f (pushSpawns own pend).1, (pushSpawns own pend).2) := by
  intro own
  induction own with
  | done x => intro pend; rfl
  | ask i k ih => intro pend; rfl
  | spawn c nxt ih => intro pend; simpa [map, pushSpawns] using ih (pend ++ [(c, none)])

theorem finished_map (g : Y → List A → C) (f : X → Y)
    (own : BS I A X) (pend : List (I × Option A)) :
    finished g (map f own) pend =
      finished (fun x as => g (f x) as) own pend := by
  cases own <;> rfl

theorem ownCell_map (f : X → Y) (own : BS I A X) :
    ownCell (map f own) = ownCell own := by
  cases own <;> rfl

theorem stepAsk_map (f : X → Y) (own : BS I A X) (a : A) :
    stepAsk (map f own) a = map f (stepAsk own a) := by
  cases own <;> rfl

end

section Follow
variable {I A X Y C : Type} [DecidableEq I] [Inhabited A]

theorem bfollow_map (f : X → Y) (g : Y → List A → C) :
    ∀ (tr : List (I × A)) (own : BS I A X)
      (pend : List (I × Option A)) (T : Table I A),
      bfollow g tr (map f own) pend T =
        bfollow (fun x as => g (f x) as) tr own pend T := by
  intro tr
  induction tr with
  | nil =>
      intro own pend T
      simp only [bfollow, pushSpawns_map, finished_map]
  | cons q rest ih =>
      rcases q with ⟨l, a⟩
      intro own pend T
      simp only [bfollow, pushSpawns_map, finished_map, ownCell_map, stepAsk_map]
      cases hf : finished (fun x as => g (f x) as)
          (pushSpawns own pend).1 (pushSpawns own pend).2 with
      | none =>
          by_cases hown : ownCell (pushSpawns own pend).1 = some l
          · by_cases hwait : waits l (pushSpawns own pend).2 = true
            · by_cases ht : T l = none <;> simp [hf, hown, hwait, ht, ih]
            · by_cases ht : T l = none <;> simp [hf, hown, hwait, ht, ih]
          · by_cases hwait : waits l (pushSpawns own pend).2 = true
            · by_cases ht : T l = none <;> simp [hf, hown, hwait, ht, ih]
            · by_cases ht : T l = none <;> simp [hf, hown, hwait, ht, ih]
      | some c => simp [hf]

end Follow

section Law
variable {I A X Y C : Type} [DecidableEq I] [Inhabited A] [Fintype A]

theorem blaw_map (f : X → Y) (g : Y → List A → C) (obs : C → ℚ) :
    ∀ (own : BS I A X) (pend : List (I × Option A)),
      blaw g obs (map f own) pend =
        blaw (fun x as => g (f x) as) obs own pend := by
  intro own
  induction own generalizing pend with
  | done x => intro pend; rfl
  | ask i k ih =>
      intro pend
      simp only [map, blaw]
      apply mean_congr
      intro a
      exact ih a pend
  | spawn c nxt ih =>
      intro pend
      simp only [map, blaw]
      exact ih (pend ++ [(c, none)])

end Law

#print axioms map
#print axioms pushSpawns_map
#print axioms finished_map
#print axioms ownCell_map
#print axioms stepAsk_map
#print axioms bfollow_map
#print axioms blaw_map

end AspisR1.BackgroundOwnMap
