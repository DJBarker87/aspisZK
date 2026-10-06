import FS2.DuplexWalk

/-! # `DecodesSpec` for the duplex with the chain-running verifier

Outside the collision event: `absC i` is first-read before `sqC i` and
`adC i` (their 32-byte prefix is its fresh output), and `adC i` before
`absC (i+1)` (whose prefix is its output); so every earlier round's cells
are in the table at `absC i`'s first read, the walk recovers the records, the
decoded completing sampler starts at `absC i`, and — all its cells being
fresh then and read later by the verifier — `follow` completes it to the
round's prefix, message and challenge. -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

variable {M Cv X W Pf : Type} {L : Nat}

/-! ## `traceFrom` -/

section TraceFrom
variable {I A : Type} [DecidableEq I]

theorem traceFrom_eq (H : I → A) : ∀ (tr : List (I × A)) (a : I), (∀ q ∈ tr, q.2 = H q.1) →
    Read tr a → ∃ rest, traceFrom tr a = (a, H a) :: rest ∧
      (∀ q ∈ rest, q.2 = H q.1) ∧ (∀ b, Read tr b → Before tr a b → b ∈ rest.map Prod.fst) := by
  intro tr
  induction tr with
  | nil => intro a _ h; simp [Read] at h
  | cons q rest ih =>
      intro a hcons ha
      obtain ⟨i, v⟩ := q
      have hv : v = H i := hcons (i, v) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, q.2 = H q.1 := fun q hq => hcons q (List.mem_cons_of_mem _ hq)
      by_cases hia : i = a
      · subst hia
        refine ⟨rest, by simp [traceFrom, hv], hrest, ?_⟩
        intro b hrb hB
        obtain ⟨_, hlt⟩ := hB
        have hib : i ≠ b := by
          intro e; subst e; exact lt_irrefl _ hlt
        have hrb' : b ∈ i :: rest.map Prod.fst := hrb
        rcases List.mem_cons.mp hrb' with h | h
        · exact absurd h.symm hib
        · exact h
      · have ha' : Read rest a := by
          have ha'' : a ∈ i :: rest.map Prod.fst := ha
          rcases List.mem_cons.mp ha'' with h | h
          · exact absurd h.symm hia
          · exact h
        obtain ⟨r, hr, hc, hb⟩ := ih a hrest ha'
        refine ⟨r, by simp [traceFrom, hia, hr], hc, ?_⟩
        intro b hrb hB
        obtain ⟨_, hlt⟩ := hB
        have hib : i ≠ b := by
          intro e; subst e
          simp [firstIdx, hia] at hlt
        have hrb2 : Read rest b := by
          have hrb' : b ∈ i :: rest.map Prod.fst := hrb
          rcases List.mem_cons.mp hrb' with h | h
          · exact absurd h.symm hib
          · exact h
        apply hb b hrb2
        refine ⟨ha', ?_⟩
        simp only [firstIdx, hia, hib, if_false] at hlt
        omega

end TraceFrom

/-! ## Ordering of the transcript's cells -/

section Order
variable (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
  (extract : X → Table (Addr L) State → Option W) (H : Addr L → State) (π : Pf)
  (tr : List (Addr L × State)) (hcons : ∀ q ∈ tr, q.2 = H q.1) (Qtot : Nat)
  (hQ : firstReads emptyTable tr ≤ Qtot) (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
  (r : Nat)
  (hread : ∀ j < r, Read tr (absC p x msg extract H π j) ∧ Read tr (sqC p x msg extract H π j) ∧
    Read tr (adC p x msg extract H π j))

include hcons hQ hcoll hread

theorem abs_before_sq (i : Nat) (hi : i < r) :
    Before tr (absC p x msg extract H π i) (sqC p x msg extract H π i) :=
  noColl_prefix_after p Qtot H tr hcons hQ hcoll _ _ (hread i hi).1 (hread i hi).2.1 (toBytes_squeezeA p _)

theorem abs_before_ad (i : Nat) (hi : i < r) :
    Before tr (absC p x msg extract H π i) (adC p x msg extract H π i) :=
  noColl_prefix_after p Qtot H tr hcons hQ hcoll _ _ (hread i hi).1 (hread i hi).2.2 (toBytes_advanceA p _)

theorem ad_before_abs (i : Nat) (hi : i + 1 < r) :
    Before tr (adC p x msg extract H π i) (absC p x msg extract H π (i + 1)) := by
  apply noColl_prefix_after p Qtot H tr hcons hQ hcoll _ _ (hread i (by omega)).2.2 (hread (i + 1) hi).1
  rw [absC, toBytes_absorbA, sv_succ]

theorem abs_before_abs : ∀ j i, j < i → i < r →
    Before tr (absC p x msg extract H π j) (absC p x msg extract H π i) := by
  intro j i hji hi
  induction i with
  | zero => omega
  | succ i ih =>
      have h1 := before_trans tr
        (abs_before_ad p x msg extract H π tr hcons Qtot hQ hcoll r hread i (by omega))
        (ad_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread i hi)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hji with h | h
      · exact before_trans tr (ih h (by omega)) h1
      · subst h; exact h1

theorem ad_before_abs' (j i : Nat) (hji : j < i) (hi : i < r) :
    Before tr (adC p x msg extract H π j) (absC p x msg extract H π i) := by
  rcases Nat.lt_iff_add_one_le.mp hji |>.lt_or_eq with h | h
  · exact before_trans tr
      (ad_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread j (by omega))
      (abs_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread _ _ h hi)
  · rw [← h]; exact ad_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread j (h ▸ hi)

/-- The absorbed states of distinct rounds differ. -/
theorem sv'_ne (j i : Nat) (hji : j < i) (hi : i < r) :
    sv' p x msg extract H π j ≠ sv' p x msg extract H π i := by
  apply noColl_injective p Qtot H tr hcons hQ hcoll _ _ (hread j (by omega)).1 (hread i hi).1
  exact before_ne tr (abs_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread j i hji hi)

end Order

end
end FS2.Duplex
