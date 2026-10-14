import FS2.Verifier

/-! A verifier whose terminal decision may perform oracle reads. -/
set_option autoImplicit false
namespace AspisR1.OracleVerifier

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]

/-- Run the remaining rounds and then run an oracle-reading terminal decision. -/
def verifierFrom (pr : FS2.Protocol X M C W Pf I A)
    (decision : Prefix X M C → M → Program I A Bool) (π : Pf) :
    Nat → Prefix X M C → Program I A Bool
  | 0, P => decision P (pr.msg π pr.r)
  | n + 1, P =>
      bind ((pr.samp (pr.r - (n + 1)) P (pr.msg π (pr.r - (n + 1)))).toProgram) fun c =>
        verifierFrom pr decision π n (P.ext (pr.msg π (pr.r - (n + 1))) c)

/-- Run every round and then the terminal decision. -/
def verifier (pr : FS2.Protocol X M C W Pf I A)
    (decision : Prefix X M C → M → Program I A Bool) (x : X) (π : Pf) :
    Program I A Bool :=
  verifierFrom pr decision π pr.r (emptyPrefix x)

/-- The trace is all remaining chain traces followed by the terminal trace. -/
theorem verifierFrom_eval (pr : FS2.Protocol X M C W Pf I A)
    (decision : Prefix X M C → M → Program I A Bool)
    (H : I → A) (x : X) (π : Pf) :
    ∀ n, n ≤ pr.r →
      eval H (verifierFrom pr decision π n (pr.transcript H x π (pr.r - n))) =
        ((((List.range n).map fun j =>
          (eval H (pr.chain H x π (pr.r - n + j)).toProgram).1).flatten ++
          (eval H (decision (pr.transcript H x π pr.r) (pr.msg π pr.r))).1),
          (eval H (decision (pr.transcript H x π pr.r) (pr.msg π pr.r))).2) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [verifierFrom, eval]
  | succ n ih =>
      intro hn
      have hi : pr.r - (n + 1) + 1 = pr.r - n := by omega
      simp only [verifierFrom]
      rw [eval_bind]
      dsimp only
      have hstep :
          (pr.transcript H x π (pr.r - (n + 1))).ext
              (pr.msg π (pr.r - (n + 1)))
              ((eval H ((pr.samp (pr.r - (n + 1))
                (pr.transcript H x π (pr.r - (n + 1)))
                (pr.msg π (pr.r - (n + 1)))).toProgram)).2) =
            pr.transcript H x π (pr.r - n) := by
        rw [← hi]
        rfl
      rw [hstep, ih (by omega)]
      refine Prod.ext ?_ rfl
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
        List.flatten_cons, FS2.Protocol.chain]
      simp only [List.append_assoc]
      congr 1
      congr 1
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      have hj : pr.r - (n + 1) + (j + 1) = pr.r - n + j := by omega
      rw [hj]

theorem verifier_eval (pr : FS2.Protocol X M C W Pf I A)
    (decision : Prefix X M C → M → Program I A Bool)
    (H : I → A) (x : X) (π : Pf) :
    eval H (verifier pr decision x π) =
      (((List.range pr.r).map fun j =>
        (eval H (pr.chain H x π j).toProgram).1).flatten ++
        (eval H (decision (pr.transcript H x π pr.r) (pr.msg π pr.r))).1,
        (eval H (decision (pr.transcript H x π pr.r) (pr.msg π pr.r))).2) := by
  have h := verifierFrom_eval pr decision H x π pr.r le_rfl
  simp only [Nat.sub_self, zero_add] at h
  change eval H (verifierFrom pr decision π pr.r (emptyPrefix x)) = _ at h
  unfold verifier
  exact h

/-- Every chain read lies in the full verifier trace. -/
theorem verifier_chain_reads (pr : FS2.Protocol X M C W Pf I A)
    (decision : Prefix X M C → M → Program I A Bool)
    (H : I → A) (x : X) (π : Pf) (i : Nat) (hi : i < pr.r) (a : I)
    (ha : a ∈ (eval H (pr.chain H x π i).toProgram).1.map Prod.fst) :
    a ∈ (eval H (verifier pr decision x π)).1.map Prod.fst := by
  rw [verifier_eval]
  simp only [List.map_append, List.mem_append, List.map_flatten, List.map_map,
    List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl ⟨_, ⟨i, hi, rfl⟩, ha⟩

/-- Every terminal-decision read lies in the full verifier trace. -/
theorem verifier_terminal_reads (pr : FS2.Protocol X M C W Pf I A)
    (decision : Prefix X M C → M → Program I A Bool)
    (H : I → A) (x : X) (π : Pf) (a : I)
    (ha : a ∈ (eval H
      (decision (pr.transcript H x π pr.r) (pr.msg π pr.r))).1.map Prod.fst) :
    a ∈ (eval H (verifier pr decision x π)).1.map Prod.fst := by
  rw [verifier_eval]
  simp only [List.map_append, List.mem_append]
  exact Or.inr ha

/-- A terminal `.done` decision specializes to the original FS2 verifier. -/
theorem verifier_specializes_done (pr : FS2.Protocol X M C W Pf I A)
    (decision : Prefix X M C → M → Bool) (x : X) (π : Pf) :
    verifier pr (fun P m => Program.done (decision P m)) x π =
      FS2.verifier pr decision x π := by
  unfold verifier FS2.verifier
  have hfrom : ∀ n P,
      verifierFrom pr (fun P m => Program.done (decision P m)) π n P =
        FS2.verifierFrom pr decision π n P := by
    intro n
    induction n with
    | zero => intro P; rfl
    | succ n ih =>
        intro P
        simp only [verifierFrom, FS2.verifierFrom]
        congr 1
        funext c
        exact ih (P.ext (pr.msg π (pr.r - (n + 1))) c)
  exact hfrom pr.r (emptyPrefix x)

#print axioms verifierFrom_eval
#print axioms verifier_eval
#print axioms verifier_chain_reads
#print axioms verifier_terminal_reads
#print axioms verifier_specializes_done

end AspisR1.OracleVerifier
