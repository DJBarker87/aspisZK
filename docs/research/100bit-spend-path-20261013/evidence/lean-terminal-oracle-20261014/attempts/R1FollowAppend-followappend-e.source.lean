import R0C.V3.BS

/-! Deterministic successful-prefix preservation for the FS2 and background
sampler followers. -/
set_option autoImplicit false
namespace AspisR1.FollowAppend

open FS FS2
open R0C.V3
open AspisV8R19.MemoizedProgramLaw
open AspisV8PairedCommitment

section FS2Follow
variable {I A C : Type} [DecidableEq I] [Inhabited A]

theorem follow_append_of_some (s : Sampler I A C) (t : Table I A)
    (tr tail : List (I × A)) (c : C)
    (h : FS2.follow s t tr = some c) :
    FS2.follow s t (tr ++ tail) = some c := by
  induction tr generalizing s t with
  | nil =>
      cases s <;> simp [FS2.follow] at h ⊢
  | cons q rest ih =>
      rcases q with ⟨l, a⟩
      cases s with
      | done d => simp [FS2.follow]
      | ask i k =>
          by_cases heq : l = i
          · subst l
            by_cases hfresh : t i = none
            · simp only [FS2.follow, if_pos rfl, if_pos hfresh] at h ⊢
              exact ih (k a) (put t i a) h
            · simp [FS2.follow, hfresh] at h
          · simp only [FS2.follow, if_neg heq] at h ⊢
            exact ih (.ask i k) (put t l a) h
      | multi i cs nd k =>
          by_cases hmem : l ∈ i :: cs
          · by_cases hfresh : t l = none
            · simp only [FS2.follow, if_pos hmem, if_pos hfresh] at h ⊢
              exact ih (stepMulti i cs nd k l a) (put t l a) h
            · simp [FS2.follow, hmem, hfresh] at h
          · simp only [FS2.follow, if_neg hmem] at h ⊢
            exact ih (.multi i cs nd k) (put t l a) h

end FS2Follow

section BackgroundFollow
variable {I A X C : Type} [DecidableEq I] [Inhabited A]

theorem bfollow_append_of_some (g : X → List A → C)
    (tr tail : List (I × A)) (own : BS I A X)
    (pend : List (I × Option A)) (t : Table I A) (c : C)
    (h : bfollow g tr own pend t = some c) :
    bfollow g (tr ++ tail) own pend t = some c := by
  induction tr generalizing own pend t with
  | nil =>
      cases tail with
      | nil => simpa using h
      | cons q rest =>
          rcases q with ⟨l, a⟩
          have hf : finished g (pushSpawns own pend).1 (pushSpawns own pend).2 = some c := by
            simpa [bfollow] using h
          simp [bfollow, hf]
  | cons q rest ih =>
      rcases q with ⟨l, a⟩
      let own' := (pushSpawns own pend).1
      let pend' := (pushSpawns own pend).2
      cases hf : finished g own' pend' with
      | some out =>
          have hout : out = c := by
            simpa [own', pend', bfollow, hf] using h
          simp [own', pend', bfollow, hf, hout]
      | none =>
          by_cases hown : ownCell own' = some l
          · by_cases hwait : waits l pend' = true
            · simp [own', pend', bfollow, hf, hown, hwait] at h
            · by_cases ht : t l = none
              · have hr : bfollow g rest (stepAsk own' a) pend' (put t l a) = some c := by
                  simpa [own', pend', bfollow, hf, hown, hwait, ht] using h
                simpa [own', pend', bfollow, hf, hown, hwait, ht] using
                  ih (stepAsk own' a) pend' (put t l a) hr
              · simp [own', pend', bfollow, hf, hown, hwait, ht] at h
          · by_cases hwait : waits l pend' = true
            · by_cases ht : t l = none
              · have hr : bfollow g rest own' (record l a pend') (put t l a) = some c := by
                  simpa [own', pend', bfollow, hf, hown, hwait, ht] using h
                simpa [own', pend', bfollow, hf, hown, hwait, ht] using
                  ih own' (record l a pend') (put t l a) hr
              · simp [own', pend', bfollow, hf, hown, hwait, ht] at h
            · have hr : bfollow g rest own' pend' (put t l a) = some c := by
                simpa [own', pend', bfollow, hf, hown, hwait] using h
              simpa [own', pend', bfollow, hf, hown, hwait] using
                ih own' pend' (put t l a) hr

end BackgroundFollow

#print axioms follow_append_of_some
#print axioms bfollow_append_of_some

end AspisR1.FollowAppend
