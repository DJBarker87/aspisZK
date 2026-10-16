import R0C.V3.BS

/-! Address renaming for background samplers. Independent-answer laws do not
inspect addresses; shared-oracle follow transport is supplied separately. -/
set_option autoImplicit false
namespace AspisR1.BackgroundAddressMap
open R0C.V3 FS AspisV8PairedCommitment
open AspisV8R19.OracleResampling

variable {I J A X C : Type}

def rename (f : I → J) : BS I A X → BS J A X
  | .done x => .done x
  | .ask i k => .ask (f i) (fun a => rename f (k a))
  | .spawn i n => .spawn (f i) (rename f n)

def pendMap (f : I → J) (p : List (I × Option A)) : List (J × Option A) :=
  p.map (fun q => (f q.1,q.2))

@[simp] theorem pendMap_nil (f : I → J) : pendMap f ([] : List (I × Option A)) = [] := rfl
@[simp] theorem pendMap_cons (f : I → J) (q : I × Option A) (p : List (I × Option A)) :
    pendMap f (q :: p) = (f q.1,q.2) :: pendMap f p := rfl

def AllLabels (P : I → Prop) : BS I A X → Prop
  | .done _ => True
  | .ask i k => P i ∧ ∀ a, AllLabels P (k a)
  | .spawn i n => P i ∧ AllLabels P n

def restrict (P : I → Prop) : (s : BS I A X) → AllLabels P s → BS {i // P i} A X
  | .done x, _ => .done x
  | .ask i k, h => .ask ⟨i,h.1⟩ (fun a => restrict P (k a) (h.2 a))
  | .spawn i n, h => .spawn ⟨i,h.1⟩ (restrict P n h.2)

theorem rename_restrict (P : I → Prop) (s : BS I A X) (h : AllLabels P s) :
    rename Subtype.val (restrict P s h) = s := by
  induction s with
  | done x => rfl
  | ask i k ih =>
      simp only [restrict, rename]
      congr 1
      funext a
      exact ih a (h.2 a)
  | spawn i n ih =>
      simp only [restrict, rename]
      rw [ih h.2]

theorem pendMap_append (f : I → J) (p q : List (I × Option A)) :
    pendMap f (p ++ q) = pendMap f p ++ pendMap f q := List.map_append

section Follow
variable [DecidableEq I] [DecidableEq J] [Inhabited A]

theorem pushSpawns_rename (f : I → J) (s : BS I A X) (p : List (I × Option A)) :
    pushSpawns (rename f s) (pendMap f p) =
      (rename f (pushSpawns s p).1, pendMap f (pushSpawns s p).2) := by
  induction s generalizing p with
  | done x => rfl
  | ask i k ih => rfl
  | spawn i n ih =>
      simp only [rename, pushSpawns]
      have h := ih (p ++ [(i,none)])
      rw [pendMap_append, pendMap_cons, pendMap_nil] at h
      exact h

theorem allDone_pendMap (f : I → J) (p : List (I × Option A)) :
    allDone (pendMap f p) = allDone p := by
  induction p with
  | nil => rfl
  | cons q p ih => cases q with | mk i a => cases a <;> simp [allDone, ih]

theorem answers_pendMap (f : I → J) (p : List (I × Option A)) :
    answers (pendMap f p) = answers p := by simp [answers, pendMap, List.map_map]

theorem finished_rename (f : I → J) (g : X → List A → C)
    (s : BS I A X) (p : List (I × Option A)) :
    finished g (rename f s) (pendMap f p) = finished g s p := by
  cases s <;> simp [rename, finished, allDone_pendMap, answers_pendMap]

theorem ownCell_rename (f : I → J) (s : BS I A X) :
    ownCell (rename f s) = (ownCell s).map f := by cases s <;> rfl

theorem stepAsk_rename (f : I → J) (s : BS I A X) (a : A) :
    stepAsk (rename f s) a = rename f (stepAsk s a) := by cases s <;> rfl

theorem waits_pendMap (f : I → J) (hf : Function.Injective f)
    (i : I) (p : List (I × Option A)) :
    waits (f i) (pendMap f p) = waits i p := by
  induction p with
  | nil => rfl
  | cons q p ih => cases q with | mk j a => cases a <;> simp [waits, hf.eq_iff, ih]

theorem record_pendMap (f : I → J) (hf : Function.Injective f)
    (i : I) (a : A) (p : List (I × Option A)) :
    record (f i) a (pendMap f p) = pendMap f (record i a p) := by
  induction p with
  | nil => rfl
  | cons q p ih =>
      cases q with | mk j b =>
        cases b with
        | none => by_cases h : j = i <;> simp [record, hf.eq_iff, h, ih]
        | some b => simp [record, ih]

end Follow
section Law
variable [DecidableEq I] [DecidableEq J] [Inhabited A] [Fintype A]

theorem pmean_pendMap (f : I → J) (obs : List A → ℚ) (p : List (I × Option A)) :
    pmean obs (pendMap f p) = pmean obs p := by
  induction p generalizing obs with
  | nil => rfl
  | cons q p ih =>
      cases q with | mk i a =>
        cases a with
        | none => simp only [pendMap_cons, pmean]; exact mean_congr (fun a => ih _)
        | some a => exact ih _

theorem blaw_rename (f : I → J) (g : X → List A → C) (obs : C → ℚ)
    (s : BS I A X) (p : List (I × Option A)) :
    blaw g obs (rename f s) (pendMap f p) = blaw g obs s p := by
  induction s generalizing p with
  | done x => exact pmean_pendMap f _ p
  | ask i k ih =>
      simp only [rename, blaw]
      exact mean_congr (fun a => ih a p)
  | spawn i n ih =>
      simp only [rename, blaw]
      have h := ih (p ++ [(i,none)])
      rw [pendMap_append, pendMap_cons, pendMap_nil] at h
      exact h
end Law

#print axioms rename_restrict
#print axioms pushSpawns_rename
#print axioms finished_rename
#print axioms waits_pendMap
#print axioms record_pendMap
#print axioms blaw_rename
end AspisR1.BackgroundAddressMap
