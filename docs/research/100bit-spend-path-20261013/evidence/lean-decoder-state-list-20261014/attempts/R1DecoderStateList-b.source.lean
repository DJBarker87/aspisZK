import R1BackgroundOwnMap
import R0C.V3.Gen

/-! Generic adapter that represents a state-valued decoder own output as a
singleton state list. Follow and law behavior are inherited by result mapping. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DecoderStateList

open FS FS2 R0C.V3
open AspisR1.BackgroundOwnMap
open AspisV8PairedCommitment
open AspisV8R19.OracleResampling

variable {X M C I A : Type} [DecidableEq I] [Inhabited A]

def lift (dec : Dec X M C I A A) : Dec X M C I A (List A) :=
  fun i T => (dec i T).map fun (own, pend, g) =>
    (BackgroundOwnMap.map (fun x => [x]) own, pend,
      fun xs as => g (xs.headD default) as)

theorem lift_of_decode (dec : Dec X M C I A A) (i : I) (T : Table I A)
    (own : BS I A A) (pend : List (I × Option A))
    (g : A → List A → Prefix X M C × M × C)
    (h : dec i T = some (own, pend, g)) :
    lift dec i T = some
      (BackgroundOwnMap.map (fun x => [x]) own, pend,
        fun xs as => g (xs.headD default) as) := by
  simp [lift, h]

theorem lift_sound (dec : Dec X M C I A A) (i : I) (T : Table I A)
    (own : BS I A (List A)) (pend : List (I × Option A))
    (g : List A → List A → Prefix X M C × M × C)
    (h : lift dec i T = some (own, pend, g)) :
    ∃ (own₀ : BS I A A) (pend₀ : List (I × Option A))
      (g₀ : A → List A → Prefix X M C × M × C),
      dec i T = some (own₀, pend₀, g₀) ∧
      (BackgroundOwnMap.map (fun x => [x]) own₀, pend₀,
        fun xs as => g₀ (xs.headD default) as) = (own, pend, g) := by
  unfold lift at h
  cases hd : dec i T with
  | none => simp [hd] at h
  | some result =>
      rcases result with ⟨own₀, pend₀, g₀⟩
      simp only [hd] at h
      have heq := Option.some.inj h
      refine ⟨own₀, pend₀, g₀, hd, ?_⟩
      exact heq

section Follow
variable {I A X M C : Type} [DecidableEq I] [Inhabited A]

theorem lifted_follow (g : A → List A → Prefix X M C × M × C)
    (tr : List (I × A)) (own : BS I A A)
    (pend : List (I × Option A)) (T : Table I A) :
    bfollow (fun xs as => g (xs.headD default) as) tr
      (BackgroundOwnMap.map (fun x => [x]) own) pend T =
    bfollow g tr own pend T := by
  have h := BackgroundOwnMap.bfollow_map (fun x : A => [x])
    (fun xs as => g (xs.headD default) as) tr own pend T
  simpa using h
end Follow

section Law
variable {I A X M C : Type} [DecidableEq I] [Inhabited A] [Fintype A]

theorem lifted_law (g : A → List A → Prefix X M C × M × C)
    (obs : Prefix X M C × M × C → ℚ) (own : BS I A A)
    (pend : List (I × Option A)) :
    blaw (fun xs as => g (xs.headD default) as) obs
      (BackgroundOwnMap.map (fun x => [x]) own) pend =
    blaw g obs own pend := by
  have h := BackgroundOwnMap.blaw_map (fun x : A => [x])
    (fun xs as => g (xs.headD default) as) obs own pend
  simpa using h
end Law

#print axioms lift_of_decode
#print axioms lift_sound
#print axioms lifted_follow
#print axioms lifted_law

end AspisR1.DecoderStateList
end
