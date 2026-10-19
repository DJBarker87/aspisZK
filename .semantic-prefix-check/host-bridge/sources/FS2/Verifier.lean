import FS2.Theorem

/-! # A chain-running verifier, and following a fresh `multi` to completion

`verifier pr decision x π` runs every round's sampler program in order (so
its trace contains every chain cell) and then decides on the complete
transcript.  `follow_multi_complete`: a `multi` whose cells are all absent
from the table and all read later on a consistent trace is followed to its
continuation on the oracle's values. -/
set_option autoImplicit false
namespace FS2

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8PairedCommitment

section Verifier
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]

/-- Run the remaining `n` rounds from the prefix of round `r - n`, then decide. -/
def verifierFrom (pr : Protocol X M C W Pf I A) (decision : Prefix X M C → M → Bool) (π : Pf) :
    Nat → Prefix X M C → Program I A Bool
  | 0, P => .done (decision P (pr.msg π pr.r))
  | n + 1, P =>
      bind (pr.samp (pr.r - (n + 1)) P (pr.msg π (pr.r - (n + 1)))).toProgram fun c =>
        verifierFrom pr decision π n (P.ext (pr.msg π (pr.r - (n + 1))) c)

def verifier (pr : Protocol X M C W Pf I A) (decision : Prefix X M C → M → Bool) (x : X)
    (π : Pf) : Program I A Bool :=
  verifierFrom pr decision π pr.r (emptyPrefix x)

/-- The verifier's trace is the concatenation of the chains' traces. -/
theorem verifierFrom_eval (pr : Protocol X M C W Pf I A) (decision : Prefix X M C → M → Bool)
    (H : I → A) (x : X) (π : Pf) :
    ∀ n, n ≤ pr.r →
      eval H (verifierFrom pr decision π n (pr.transcript H x π (pr.r - n))) =
        (((List.range n).map fun j => (eval H (pr.chain H x π (pr.r - n + j)).toProgram).1).flatten,
          decision (pr.transcript H x π pr.r) (pr.msg π pr.r)) := by
  intro n
  induction n with
  | zero => intro _; simp [verifierFrom, eval]
  | succ n ih =>
      intro hn
      have hi : pr.r - (n + 1) + 1 = pr.r - n := by omega
      simp only [verifierFrom]
      rw [eval_bind]
      dsimp only
      have hstep : (pr.transcript H x π (pr.r - (n + 1))).ext (pr.msg π (pr.r - (n + 1)))
          (eval H (pr.samp (pr.r - (n + 1)) (pr.transcript H x π (pr.r - (n + 1)))
            (pr.msg π (pr.r - (n + 1)))).toProgram).2 = pr.transcript H x π (pr.r - n) := by
        rw [← hi]; rfl
      rw [hstep, ih (by omega)]
      refine Prod.ext ?_ rfl
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons,
        Protocol.chain]
      congr 1
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      have : pr.r - (n + 1) + (j + 1) = pr.r - n + j := by omega
      rw [this]

theorem verifier_eval (pr : Protocol X M C W Pf I A) (decision : Prefix X M C → M → Bool)
    (H : I → A) (x : X) (π : Pf) :
    eval H (verifier pr decision x π) =
      (((List.range pr.r).map fun j => (eval H (pr.chain H x π j).toProgram).1).flatten,
        decision (pr.transcript H x π pr.r) (pr.msg π pr.r)) := by
  have h := verifierFrom_eval pr decision H x π pr.r le_rfl
  simp only [Nat.sub_self, zero_add] at h
  exact h

/-- Every cell of every chain's own trace is in the verifier's trace. -/
theorem verifier_reads (pr : Protocol X M C W Pf I A) (decision : Prefix X M C → M → Bool)
    (H : I → A) (x : X) (π : Pf) (i : Nat) (hi : i < pr.r) (a : I)
    (ha : a ∈ (eval H (pr.chain H x π i).toProgram).1.map Prod.fst) :
    a ∈ (eval H (verifier pr decision x π)).1.map Prod.fst := by
  rw [verifier_eval]
  simp only [List.map_flatten, List.map_map, List.mem_flatten, List.mem_map, List.mem_range]
  exact ⟨_, ⟨i, hi, rfl⟩, ha⟩

end Verifier

section Multi
variable {I A C : Type} [DecidableEq I] [Inhabited A]

/-- A fresh `multi` all of whose cells are read later is followed to its
continuation on the oracle's values. -/
theorem follow_multi_complete (H : I → A) :
    ∀ (tr : List (I × A)) (g : (I → A) → C) (t : Table I A) (c : I) (cs : List I)
      (nd : (c :: cs).Nodup),
      (∀ q ∈ tr, q.2 = H q.1) →
      (∀ x ∈ c :: cs, t x = none ∧ x ∈ tr.map Prod.fst) →
      follow (.multi c cs nd fun acc => .done (g acc)) t tr = some (g (accOf H (c :: cs) default)) := by
  intro tr
  induction tr with
  | nil =>
      intro g t c cs nd _ h
      have := (h c (List.mem_cons_self ..)).2
      simp at this
  | cons q rest ih =>
      intro g t c cs nd hcons h
      obtain ⟨l, a⟩ := q
      have ha : a = H l := hcons (l, a) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, q.2 = H q.1 := fun q hq => hcons q (List.mem_cons_of_mem _ hq)
      simp only [follow]
      by_cases hl : l ∈ c :: cs
      · rw [if_pos hl, if_pos (h l hl).1]
        unfold stepMulti
        split
        · rename_i herase
          -- the only cell was `l`
          have hcells : c :: cs = [l] := by
            have hlen := congrArg List.length herase
            rw [List.length_erase_of_mem hl] at hlen
            simp only [List.length_cons, List.length_nil] at hlen
            have hcs : cs = [] := List.length_eq_zero_iff.mp (by omega)
            subst hcs
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rw [hl]
          rw [follow_done, ha]
          congr 2
          rw [hcells]
          funext i
          by_cases hil : i = l
          · subst hil; simp [accOf_apply]
          · simp [accOf_apply, Function.update_of_ne hil, hil]
        · rename_i c' cs' herase
          have hsub : ∀ x ∈ c' :: cs', (put t l a) x = none ∧ x ∈ rest.map Prod.fst := by
            intro x hx
            have hx' : x ∈ (c :: cs).erase l := herase ▸ hx
            have hxl : x ≠ l := by
              intro hxl; subst hxl
              exact (List.Nodup.not_mem_erase nd (a := x)) hx' |>.elim
            refine ⟨?_, ?_⟩
            · rw [put, if_neg hxl]
              exact (h x (List.mem_of_mem_erase hx')).1
            · have := (h x (List.mem_of_mem_erase hx')).2
              simp only [List.map_cons, List.mem_cons] at this
              exact this.resolve_left hxl
          beta_reduce
          rw [ih (fun acc => g (Function.update acc l a)) (put t l a) c' cs' _ hrest hsub, ha]
          congr 2
          funext i
          by_cases hil : i = l
          · subst hil; simp [accOf_apply, hl]
          · rw [Function.update_of_ne hil, accOf_apply, accOf_apply]
            have hmem : i ∈ c' :: cs' ↔ i ∈ c :: cs := by
              rw [← herase]
              constructor
              · exact List.mem_of_mem_erase
              · intro hi; exact (List.mem_erase_of_ne hil).mpr hi
            simp only [hmem]
      · rw [if_neg hl]
        apply ih g
        · exact hrest
        · intro x hx
          have hxl : x ≠ l := fun e => hl (e ▸ hx)
          refine ⟨?_, ?_⟩
          · rw [put, if_neg hxl]; exact (h x hx).1
          · have := (h x hx).2
            simp only [List.map_cons, List.mem_cons] at this
            exact this.resolve_left hxl

end Multi
end FS2
