import FS.Statement

/-! Generic no-hit bookkeeping for a list of message/challenge rounds.  The
relation and bad-round predicate remain explicit; this file makes no
probability or protocol-specific claim. -/
set_option autoImplicit false

namespace AspisR1.GenericNoHit

variable {X M C W I A : Type}

/-- A bad event occurs at the current round or in the remaining suffix. -/
def hitFrom (bad : FS.Prefix X M C → M → C → Prop) (x : X)
    (prev : List (M × C)) : List (M × C) → Prop
  | [] => False
  | (m, c) :: rest => bad ⟨x, prev⟩ m c ∨ hitFrom bad x (prev ++ [(m, c)]) rest

/-- A prefix is doomed when the relation has no witness and its existing
round list contains no bad event. -/
def doomed (bad : FS.Prefix X M C → M → C → Prop)
    (relation : X → W → Prop) (P : FS.Prefix X M C) : Prop :=
  (¬ ∃ w, relation P.statement w) ∧ ¬ hitFrom bad P.statement [] P.rounds

/-- Split a concatenated list at the boundary between its two parts. -/
theorem hitFrom_append (bad : FS.Prefix X M C → M → C → Prop)
    (x : X) (prev xs ys : List (M × C)) :
    hitFrom bad x prev (xs ++ ys) ↔
      hitFrom bad x prev xs ∨ hitFrom bad x (prev ++ xs) ys := by
  induction xs generalizing prev with
  | nil => simp [hitFrom]
  | cons q xs ih =>
      rcases q with ⟨m, c⟩
      simp only [List.cons_append, hitFrom]
      rw [ih]
      simp only [List.append_assoc]
      tauto

/-- If an extension escapes doomedness, its new round must be bad. -/
theorem doomed_ext_bad
    (bad : FS.Prefix X M C → M → C → Prop)
    (relation : X → W → Prop)
    (P : FS.Prefix X M C) (m : M) (c : C)
    (hdoomed : doomed bad relation P)
    (hnot : ¬ doomed bad relation (P.ext m c)) :
    bad P m c := by
  rcases hdoomed with ⟨hrel, hprior⟩
  have hhit : hitFrom bad P.statement [] (P.rounds ++ [(m, c)]) := by
    by_contra hno
    apply hnot
    exact ⟨hrel, by simpa only [FS.Prefix.ext] using hno⟩
  rw [hitFrom_append] at hhit
  rcases hhit with hprior' | hcurrent
  · exact (hprior hprior').elim
  · simpa only [hitFrom, List.nil_append, List.append_nil, or_false] using hcurrent

/-- Select a witness when one exists. This is a specification-level
noncomputable choice, separate from any executable checker. -/
noncomputable def chooseWitness (relation : X → W → Prop) (x : X) : Option W :=
  by
    classical
    exact if h : ∃ w, relation x w then some (Classical.choose h) else none

theorem chooseWitness_eq_none_iff
    (relation : X → W → Prop) (x : X) :
    chooseWitness relation x = none ↔ ¬ ∃ w, relation x w := by
  classical
  unfold chooseWitness
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The empty prefix is doomed exactly when the selector has no witness. -/
theorem empty_doomed
    (bad : FS.Prefix X M C → M → C → Prop)
    (relation : X → W → Prop) (x : X) :
    doomed bad relation (FS.emptyPrefix x) ↔ chooseWitness relation x = none := by
  classical
  unfold doomed FS.emptyPrefix hitFrom
  rw [chooseWitness_eq_none_iff]
  simp

theorem returned_relation
    (relation : X → W → Prop) (x : X) (w : W)
    (h : chooseWitness relation x = some w) : relation x w := by
  classical
  unfold chooseWitness at h
  split_ifs at h with hex
  · have hw : Classical.choose hex = w := Option.some.inj h
    subst w
    exact Classical.choose_spec hex

#print axioms hitFrom_append
#print axioms doomed_ext_bad
#print axioms chooseWitness_eq_none_iff
#print axioms empty_doomed
#print axioms returned_relation

end AspisR1.GenericNoHit
