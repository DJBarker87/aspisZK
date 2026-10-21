import R1Z.SimCostIdeal

/-! Fixing protocol outputs does not constrain post-proof adversary addresses.
This obstruction is independent of all field, encoding and preparation choices.
It concerns the actual Sizes contract and charged replay, not adversary work. -/
set_option autoImplicit false
namespace R1Z.SimCostAddressObstruction
open R0Z.FsStatement R1Z.GamesR1 R1Z.SimCostReplay R1Z.SimCostIdeal

/-- One legal oracle query, independent of published data. -/
def longQuery {K CommitHandle Aux : Type} [Field K] (n : Nat) :
    R1Adv K CommitHandle Aux where
  prog := fun _ _ => .query (List.replicate n 0) (fun _ => .done)
  decide := fun _ => false

theorem query_not_bounded (O : List UInt8 → OracleAnswer) (L q : Nat)
    (hq : 0 < q) :
    ¬ AddressBound O L (.query (List.replicate (L+1) 0) (fun _ => .done)) q := by
  cases q with
  | zero => omega
  | succ q =>
    intro hb
    have h := hb.1
    simp only [List.length_replicate] at h
    omega

/-- No table/encoding/preparation choice can satisfy Sizes for every adversary
at a positive query budget. Aux can already be the fixed protocol output type. -/
theorem sizes_impossible {K CommitHandle Aux : Type} [Field K]
    (W : R1Wire K CommitHandle Aux) (hq : 0 < W.qmax)
    (L T : Nat) (s : Prepared K CommitHandle Aux) :
    ¬ Sizes W L T (longQuery (L+1)) s := by
  intro hs
  exact query_not_bounded _ L W.qmax hq hs.2.2

theorem no_uniform_sizes {K CommitHandle Aux : Type} [Field K]
    (W : R1Wire K CommitHandle Aux) (hq : 0 < W.qmax)
    (L T : Nat) (s : Prepared K CommitHandle Aux) :
    ¬ ∀ adv : R1Adv K CommitHandle Aux, Sizes W L T adv s := by
  intro hs
  exact sizes_impossible W hq L T s (hs (longQuery (L+1)))

/-- The existing lookup tariff charges the whole query at its first row,
even when the stored keys themselves have fixed bounded widths. -/
theorem lookup_charges_address (a b : List UInt8) (v : OracleAnswer) (t : Table) :
    a.length ≤ (lookup a ((b,v)::t)).2 := by
  simp only [lookup]
  split <;> dsimp only <;> omega

theorem replay_charges_address (a b : List UInt8) (v : OracleAnswer)
    (t : Table) (H : List UInt8 → OracleAnswer) (q : Nat) :
    a.length ≤ (replay ((b,v)::t) H (.query a (fun _ => .done)) (q+1)).2 := by
  have hl := lookup_charges_address a b v t
  change a.length ≤ (lookup a ((b,v)::t)).2 + 1 +
    (replay ((b,v)::t) H .done q).2 + 2
  omega

/-- The actual finish cost exceeds every constant for some one-query adversary
whenever the preparation table is nonempty. This is stronger than failure of
one sufficient upper-bound contract. -/
theorem finish_unbounded {K CommitHandle Aux : Type} [Field K]
    (W : R1Wire K CommitHandle Aux) (hq : 0 < W.qmax)
    (s : Prepared K CommitHandle Aux) (ht : s.table ≠ []) (bound : Nat) :
    ∃ adv : R1Adv K CommitHandle Aux, bound < (finish W adv s).2 := by
  refine ⟨longQuery (bound+1), ?_⟩
  obtain ⟨view, table, fallback⟩ := s
  cases table with
  | nil => exact False.elim (ht rfl)
  | cons row tail =>
    obtain ⟨b,v⟩ := row
    obtain ⟨q, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    have hl := replay_charges_address (List.replicate (bound+1) 0) b v tail fallback q
    simp only [List.length_replicate] at hl
    simp only [finish, programmed, longQuery]
    rw [he]
    change bound+1 ≤ (replay ((b,v)::tail) fallback
      (.query (List.replicate (bound+1) 0) (fun _ => .done)) q.succ).2 at hl
    omega

#print axioms query_not_bounded
#print axioms sizes_impossible
#print axioms no_uniform_sizes
#print axioms lookup_charges_address
#print axioms replay_charges_address
#print axioms finish_unbounded
end R1Z.SimCostAddressObstruction
