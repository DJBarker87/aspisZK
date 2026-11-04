import R1Z.ProverCommitSimulatorSeedGuess18
import R1Z.QueryScanFreshNumerics
import R1Z.RomObserverBin
/-! A retained independent seed and a single, global seed-query event.
The event conservatively covers the entire simulator coin namespace: a query
with the exact domain and seed prefix is charged even if its suffix is malformed.
No independence of a source seed from its observed execution is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSeedEvent19
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.LawTransport
open R1Z.ProverCommitSimulatorCoin18 R1Z.ProverCommitSimulatorOracle18
attribute [local instance] Classical.propDecidable

abbrev Entry := List UInt8 × OracleAnswer

def seedPoint (a : List UInt8) (seed : OracleAnswer) : Prop :=
  a.take ((domain.val.map ProverCommitSaltBytes.byte).length + 32) =
    domain.val.map ProverCommitSaltBytes.byte ++ List.ofFn seed

theorem seedPoint_unique (a : List UInt8) {s t : OracleAnswer}
    (hs : seedPoint a s) (ht : seedPoint a t) : s = t := by
  have he := List.append_cancel_left (hs.symm.trans ht)
  simpa only [List.ofFn_inj] using he

theorem source_point (s : OracleAnswer) (attempt : Nat) (stream : UInt8) (counter : Nat) :
    seedPoint (address (List.ofFn s) attempt stream counter) s := by
  have take_prefix (p t rest : List UInt8) (ht : t.length = 32) :
      (p ++ t ++ rest).take (p.length + 32) = p ++ t := by
    rw [← ht, ← List.length_append, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  unfold seedPoint address
  simpa only [List.append_assoc] using
    take_prefix (domain.val.map ProverCommitSaltBytes.byte) (List.ofFn s)
      (TranscriptR1.le32 attempt ++ [stream] ++ LayoutR1PBin.le64 counter)
      (by simp only [List.length_ofFn])

def seedGuess (queries : List Entry) (seed : OracleAnswer) : Prop :=
  ∃ entry ∈ queries, seedPoint entry.1 seed

def budget (q : Nat) : ℚ := (q : ℚ) / (2 : ℚ)^256

theorem point_mass_le (a : List UInt8) :
    eventMass (seedPoint a) ≤ 1 / (2 : ℚ)^256 := by
  by_cases exists_seed : ∃ s, seedPoint a s
  · obtain ⟨s, hs⟩ := exists_seed
    have hm := eventMass_mono (seedPoint a) (fun t => t = s)
      (fun t ht => seedPoint_unique a ht hs)
    rw [QueryScanSharedHistoryMass.point_mass, QueryScanSharedHistoryMass.answer_cardinality,
      Nat.cast_pow, Nat.cast_ofNat] at hm
    exact hm
  · have empty : seedPoint a = fun _ => False := by
      funext s
      exact propext ⟨fun hs => exists_seed ⟨s, hs⟩, False.elim⟩
    rw [empty]
    simp only [eventMass, if_false, mean_const]
    positivity

theorem list_mass (queries : List Entry) :
    eventMass (seedGuess queries) ≤ budget queries.length := by
  induction queries with
  | nil => simp only [seedGuess, List.not_mem_nil, false_and, exists_false,
      eventMass, if_false, mean_const, budget, List.length_nil, Nat.cast_zero, zero_div, le_refl]
  | cons a tail ih =>
    have eqv : seedGuess (a::tail) = fun s => seedPoint a.1 s ∨ seedGuess tail s := by
      funext s
      simp only [seedGuess, List.mem_cons, exists_eq_or_imp]
    rw [eqv]
    have h := (R0Z.FsAbortBounds.mass_or_le _ _).trans (add_le_add (point_mass_le a.1) ih)
    change eventMass (fun s => seedPoint a.1 s ∨ seedGuess tail s) ≤ _ at h
    apply h.trans
    simp only [budget, List.length_cons, Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)

theorem budget_mono {q r : Nat} (hq : q ≤ r) : budget q ≤ budget r := by
  unfold budget
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hq) (by positivity)

/-- The list may depend on every model coin and every adaptive answer, but
not on this extra independent seed. Thus one charge covers all attempts. -/
theorem seed_mass {M : Type} [Fintype M] [Nonempty M]
    (queries : M → List Entry) (q : Nat) (bound : ∀ m, (queries m).length ≤ q) :
    eventMass (fun r : M × OracleAnswer => seedGuess (queries r.1) r.2) ≤ budget q := by
  unfold eventMass
  rw [mean_product]
  have h := R0Z.FsGood.mean_le_mean
    (fun m => eventMass (seedGuess (queries m))) (fun _ => budget q)
    (fun m => (list_mass (queries m)).trans (budget_mono (bound m)))
  rw [mean_const] at h
  exact h

/-- Only attempt zero carries the global event; it is not charged eight times. -/
def augmented {M : Type} (old : Fin 8 → M → Prop) (queries : M → List Entry)
    (i : Fin 8) (r : M × OracleAnswer) : Prop :=
  old i r.1 ∨ (i = 0 ∧ seedGuess (queries r.1) r.2)

theorem old_contained {M : Type} (old : Fin 8 → M → Prop) (queries : M → List Entry)
    (i : Fin 8) (r : M × OracleAnswer) (ho : old i r.1) : augmented old queries i r :=
  Or.inl ho

theorem union_mass {M : Type} [Fintype M] [Nonempty M]
    (old : Fin 8 → M → Prop) (queries : M → List Entry) (q : Nat)
    (bound : ∀ m, (queries m).length ≤ q) :
    eventMass (fun r => ∃ i, augmented old queries i r) ≤
      eventMass (fun m => ∃ i, old i m) + budget q := by
  have sub : ∀ r : M × OracleAnswer, (∃ i, augmented old queries i r) →
      (∃ i, old i r.1) ∨ seedGuess (queries r.1) r.2 := by
    rintro r ⟨i, ho | ⟨_, hs⟩⟩
    · exact Or.inl ⟨i, ho⟩
    · exact Or.inr hs
  have h := (eventMass_mono _ _ sub).trans (R0Z.FsAbortBounds.mass_or_le _ _)
  have hm : eventMass (fun r : M × OracleAnswer => ∃ i, old i r.1) =
      eventMass (fun m => ∃ i, old i m) := by
    unfold eventMass
    rw [mean_product]
    congr 1
    funext m
    by_cases hm : ∃ i, old i m
    · simp only [if_pos hm, mean_const]
    · simp only [if_neg hm, mean_const]
  change eventMass (fun r => ∃ i, augmented old queries i r) ≤
    eventMass (fun r : M × OracleAnswer => ∃ i, old i r.1) +
      eventMass (fun r : M × OracleAnswer => seedGuess (queries r.1) r.2) at h
  rw [hm] at h
  exact h.trans (add_le_add (le_refl _) (seed_mass queries q bound))

#print axioms seedPoint_unique
#print axioms source_point
#print axioms point_mass_le
#print axioms list_mass
#print axioms budget_mono
#print axioms seed_mass
#print axioms old_contained
#print axioms union_mass
end R1Z.ProverCommitSeedEvent19
