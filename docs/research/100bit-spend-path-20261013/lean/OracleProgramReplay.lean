import R1TraceTable
import FS2.Verifier

/-! Reconstruct an oracle computation from its own finite recorded trace.
The fallback is never consulted at an address used by the original run.
This works for unrestricted address types and does not assume finite support
for the oracle itself. -/
set_option autoImplicit false
namespace AspisR1.OracleProgramReplay

open FS FS2 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw

variable {I A O : Type} [DecidableEq I]

def oracleOf [Inhabited A] (tr : List (I × A)) (a : I) : A :=
  (TraceTable.replay emptyTable tr a).getD default

theorem oracleOf_eq [Inhabited A] (H : I → A) (tr : List (I × A))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (a : I)
    (ha : a ∈ tr.map Prod.fst) : oracleOf tr a = H a := by
  unfold oracleOf
  rw [TraceTable.replay_empty_apply H tr hcons a, if_pos ha]
  rfl

/-- Agreement only on the realized reads suffices, including all adaptive
branches taken by the original program. -/
theorem eval_eq_of_agrees (H H' : I → A) (p : Program I A O)
    (h : ∀ a ∈ (eval H p).1.map Prod.fst, H' a = H a) :
    eval H' p = eval H p := by
  induction p with
  | done out => rfl
  | ask a next ih =>
      have ha : H' a = H a := h a (List.mem_cons_self ..)
      have ht : ∀ b ∈ (eval H (next (H a))).1.map Prod.fst, H' b = H b := by
        intro b hb
        exact h b (List.mem_cons_of_mem _ hb)
      simp only [eval, ha, ih (H a) ht]

theorem eval_oracleOf [Inhabited A] (H : I → A) (p : Program I A O)
    (tr : List (I × A)) (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hreads : ∀ a ∈ (eval H p).1.map Prod.fst, a ∈ tr.map Prod.fst) :
    eval (oracleOf tr) p = eval H p :=
  eval_eq_of_agrees H (oracleOf tr) p fun a ha => oracleOf_eq H tr hcons a (hreads a ha)

/-- Replaying the full verifier log reconstructs each transcript prefix.
The induction consumes only the reads of the corresponding round's chain. -/
theorem transcript_eq_of_agrees {X M C W Pf : Type} [Inhabited A]
    (pr : Protocol X M C W Pf I A) (decision : Prefix X M C → M → Bool)
    (H H' : I → A) (x : X) (pf : Pf)
    (h : ∀ a ∈ (eval H (FS2.verifier pr decision x pf)).1.map Prod.fst, H' a = H a)
    (n : Nat) (hn : n ≤ pr.r) : pr.transcript H' x pf n = pr.transcript H x pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (by omega)
      have he : eval H' (pr.chain H x pf n).toProgram =
          eval H (pr.chain H x pf n).toProgram := by
        apply eval_eq_of_agrees
        intro a ha
        exact h a (FS2.verifier_reads pr decision H x pf n (by omega) a ha)
      change (pr.transcript H' x pf n).ext (pr.msg pf n)
        (eval H' (pr.samp n (pr.transcript H' x pf n) (pr.msg pf n)).toProgram).2 = _
      rw [hp]
      change (pr.transcript H x pf n).ext (pr.msg pf n)
        (eval H' (pr.chain H x pf n).toProgram).2 = _
      rw [he]
      rfl

#print axioms oracleOf_eq
#print axioms eval_eq_of_agrees
#print axioms eval_oracleOf
#print axioms transcript_eq_of_agrees
end AspisR1.OracleProgramReplay
