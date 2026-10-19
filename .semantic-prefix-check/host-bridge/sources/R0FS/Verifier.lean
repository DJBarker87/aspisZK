import FS.Statement

/-! # A verifier that recomputes every challenge

Generic over the `FS.Protocol` interface: the verifier reads the address of
each message-ending prefix in order, derives the challenge with the round's
sampler, and finally applies a decision to the complete transcript.  Its run
on an oracle `H` visits exactly the transcript addresses and ends at
`transcript H x π r`, which gives §2's "re-reads challenge addresses" and the
shape (D3) needs. -/
set_option autoImplicit false
namespace R0FS

open FS AspisV8R19.MemoizedProgramLaw

section
variable {X M C W Pf I B : Type} {K : Nat}

/-- Read the remaining `n` rounds starting from prefix `P` of round `r - n`,
then decide. -/
def verifierFrom (pr : Protocol X M C W Pf I B K) (decision : Prefix X M C → M → Bool)
    (π : Pf) : Nat → Prefix X M C → Program I (Block B K) Bool
  | 0, P => .done (decision P (pr.msg π pr.r))
  | n + 1, P =>
      .ask (pr.addr P (pr.msg π (pr.r - (n + 1)))) fun b =>
        verifierFrom pr decision π n
          (P.ext (pr.msg π (pr.r - (n + 1))) (pr.chal (pr.r - (n + 1)) b))

def verifier (pr : Protocol X M C W Pf I B K) (decision : Prefix X M C → M → Bool)
    (x : X) (π : Pf) : Program I (Block B K) Bool :=
  verifierFrom pr decision π pr.r (emptyPrefix x)

theorem verifierFrom_eval (pr : Protocol X M C W Pf I B K)
    (decision : Prefix X M C → M → Bool) (H : I → Block B K) (x : X) (π : Pf) :
    ∀ n, n ≤ pr.r →
      eval H (verifierFrom pr decision π n (pr.transcript H x π (pr.r - n))) =
        ((List.range n).map fun j => (pr.chalAddr H x π (pr.r - n + j),
            H (pr.chalAddr H x π (pr.r - n + j))),
          decision (pr.transcript H x π pr.r) (pr.msg π pr.r)) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [verifierFrom, eval]
  | succ n ih =>
      intro hn
      have hi : pr.r - (n + 1) + 1 = pr.r - n := by omega
      simp only [verifierFrom, eval]
      have hstep : (pr.transcript H x π (pr.r - (n + 1))).ext (pr.msg π (pr.r - (n + 1)))
          (pr.chal (pr.r - (n + 1)) (H (pr.addr (pr.transcript H x π (pr.r - (n + 1)))
            (pr.msg π (pr.r - (n + 1)))))) = pr.transcript H x π (pr.r - n) := by
        rw [← hi]
        rfl
      rw [hstep, ih (by omega)]
      refine Prod.ext ?_ rfl
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Protocol.chalAddr]
      refine List.cons_eq_cons.mpr ⟨by simp, ?_⟩
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      have : pr.r - (n + 1) + (j + 1) = pr.r - n + j := by omega
      rw [this]

theorem verifier_eval (pr : Protocol X M C W Pf I B K)
    (decision : Prefix X M C → M → Bool) (H : I → Block B K) (x : X) (π : Pf) :
    eval H (verifier pr decision x π) =
      ((List.range pr.r).map fun j => (pr.chalAddr H x π j, H (pr.chalAddr H x π j)),
        decision (pr.transcript H x π pr.r) (pr.msg π pr.r)) := by
  have h := verifierFrom_eval pr decision H x π pr.r le_rfl
  simp only [Nat.sub_self, zero_add] at h
  exact h

theorem verifier_readsChallenges (pr : Protocol X M C W Pf I B K)
    (decision : Prefix X M C → M → Bool) :
    ReadsChallenges pr (verifier pr decision) := by
  intro H x π i hi
  rw [verifier_eval]
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp]
  exact ⟨i, hi, rfl⟩

theorem verifier_decision (pr : Protocol X M C W Pf I B K)
    (decision : Prefix X M C → M → Bool) (H : I → Block B K) (x : X) (π : Pf) :
    (eval H (verifier pr decision x π)).2 = decision (pr.transcript H x π pr.r) (pr.msg π pr.r) := by
  rw [verifier_eval]

end
end R0FS
