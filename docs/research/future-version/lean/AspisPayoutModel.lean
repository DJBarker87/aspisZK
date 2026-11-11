/-! The Aspis one-transaction verifier: the payout conjunct (PayoutBound,
ONE-TRANSACTION-GAME.md sections 1.2a and 9.3) over a small explicit model of
the Pool's withdrawal step.

Kind of result: MODEL THEOREMS about an explicit model written here. This is
NOT a source refinement: that the Rust (programs/aspis-pool/src/vault.rs
`plan_legacy_withdrawal_transfer_from_identity_v1` and
`validate_exact_withdrawal_delta_v1`, pair_forest.rs around the withdrawal
plan, pair_forest_dispatch.rs, and the verifier entry) computes this model is
an open obligation, stated as hypotheses below and labelled.

The model, step by step, as in the Rust:
1. the Pool decodes the request (`decode`);
2. the plan (vault.rs:387-540): nonzero amount; the five keys (mint, vault,
   destination, vault authority, token program) equal the request's
   destination, the vault and authority addresses of the request's pool and
   the pool's mint; the pre-call vault and destination token accounts parse,
   their mints are the plan's, the vault authority is the plan's, and the
   expected balances `vaultAfter = vault - amount`,
   `destAfter = dest + amount` are computed (subtraction checked);
3. the cross-program call: an ARBITRARY state change `callee`, constrained only
   by the two runtime-class trust rows R-a and R-b (hypotheses of the theorem,
   not of the model);
4. the post-call exact-delta check (vault.rs:551-580) on what the Pool reads
   after the call (`read`);
5. the state write: the step returns the post-call state.

Hypothesis classes in the composed theorem: R-a, R-b (trust rows, runtime
class); P1, E1, P2, P3 (open proof obligations about Aspis's own code; never
trust rows). -/
set_option autoImplicit false
noncomputable section
namespace AspisPayout
open Classical

variable {K B : Type}

/-- The fields of a token account the Pool reads. `rest` stands for every other
field (delegate, close authority, frozen state, lamports); the Pool's check
does not read it. -/
structure TokenAccount (K : Type) where
  mint : K
  authority : K
  amount : Nat
  rest : Nat

/-- Account data, by address; `none` = does not parse as a token account. -/
abbrev World (K : Type) := K → Option (TokenAccount K)

/-- The fields of the Pool request the payout and the statement use. -/
structure Request (K : Type) where
  pool : K
  deployment : K
  destination : K
  amount : Nat
  withdrawal : Bool

/-- The fields of the public statement the payout conjunct names: pool,
deployment domain, destination (present iff withdrawal; the has-destination
byte of the PIN2 serialization), amount. -/
structure Statement (K : Type) where
  pool : K
  deployment : K
  destination : Option K
  amount : Nat

/-- The Pool's authenticated identity of a pool: its vault and vault-authority
addresses, its asset mint, its deployment domain. -/
structure PoolIds (K : Type) where
  vaultOf : K → K
  authorityOf : K → K
  mintOf : K → K
  deploymentOf : K → K

/-- The five passed accounts (the token program key is checked separately and
plays no part in the balances). -/
structure Keys (K : Type) where
  mint : K
  vault : K
  dest : K
  authority : K

structure Plan (K : Type) where
  keys : Keys K
  amount : Nat
  vaultAfter : Nat
  destAfter : Nat

/-- The pre-call plan (vault.rs:387-540). -/
def plan (ids : PoolIds K) (r : Request K) (keys : Keys K) (w0 : World K) : Option (Plan K) :=
  if r.amount = 0 then none
  else if keys.dest = r.destination ∧ keys.vault = ids.vaultOf r.pool ∧
      keys.authority = ids.authorityOf r.pool ∧ keys.mint = ids.mintOf r.pool then
    match w0 keys.vault, w0 keys.dest with
    | some v, some d =>
      if v.mint = keys.mint ∧ d.mint = keys.mint ∧ v.authority = keys.authority ∧
          r.amount ≤ v.amount then
        some ⟨keys, r.amount, v.amount - r.amount, d.amount + r.amount⟩
      else none
    | _, _ => none
  else none

/-- The post-call exact-delta check (vault.rs:551-580). -/
def DeltaOk (p : Plan K) (view : World K) : Prop :=
  match view p.keys.vault, view p.keys.dest with
  | some v, some d => v.mint = p.keys.mint ∧ d.mint = p.keys.mint ∧
      v.authority = p.keys.authority ∧ v.amount = p.vaultAfter ∧ d.amount = p.destAfter
  | _, _ => False

/-- The Pool's withdrawal step. `callee` is the cross-program call as an
arbitrary state change; `read` is what the Pool reads after it. Returns the
post-call state on success, `none` on any rejection (the transaction fails). -/
def step (ids : PoolIds K) (r : Request K) (keys : Keys K) (w0 : World K)
    (callee : World K → World K) (read : World K → World K) : Option (World K) :=
  match plan ids r keys w0 with
  | none => none
  | some p => if DeltaOk p (read (callee w0)) then some (callee w0) else none

/-- Trust row R-a (post-call visibility, runtime class): after a cross-program
call returns Ok, the account data the caller reads is the data as the callee
left it — here, for the two accounts the Pool re-reads. -/
def RowA (keys : Keys K) (callee : World K → World K) (read : World K → World K)
    (w0 : World K) : Prop :=
  read (callee w0) keys.vault = callee w0 keys.vault ∧
    read (callee w0) keys.dest = callee w0 keys.dest

/-- Trust row R-b (writable set, runtime class): a cross-program call changes
only the accounts passed to it as writable — here the vault and the
destination. -/
def RowB (keys : Keys K) (callee : World K → World K) (w0 : World K) : Prop :=
  ∀ k, k ≠ keys.vault → k ≠ keys.dest → callee w0 k = w0 k

/-- The payout facts, about the actual pre- and post-call states. -/
structure Paid (ids : PoolIds K) (r : Request K) (keys : Keys K) (w0 w1 : World K) : Prop where
  amount_pos : 0 < r.amount
  dest_eq : keys.dest = r.destination
  vault_eq : keys.vault = ids.vaultOf r.pool
  distinct : keys.vault ≠ keys.dest
  vault_debit : ∃ v0 v1, w0 keys.vault = some v0 ∧ w1 keys.vault = some v1 ∧
    v1.amount + r.amount = v0.amount ∧ v1.mint = ids.mintOf r.pool
  dest_credit : ∃ d0 d1, w0 keys.dest = some d0 ∧ w1 keys.dest = some d1 ∧
    d1.amount = d0.amount + r.amount ∧ d1.mint = ids.mintOf r.pool
  others : ∀ k, k ≠ keys.vault → k ≠ keys.dest → w1 k = w0 k

/-- The step, if it returns Ok, moved exactly `amount` from the pool's vault to
the request's destination token account, and nothing else, given R-a and R-b. -/
theorem step_paid (ids : PoolIds K) (r : Request K) (keys : Keys K) (w0 w1 : World K)
    (callee : World K → World K) (read : World K → World K)
    (rowA : RowA keys callee read w0) (rowB : RowB keys callee w0)
    (ok : step ids r keys w0 callee read = some w1) :
    Paid ids r keys w0 w1 := by
  unfold step at ok
  cases hp : plan ids r keys w0 with
  | none => simp [hp] at ok
  | some p =>
    rw [hp] at ok
    dsimp only at ok
    by_cases hd : DeltaOk p (read (callee w0))
    · rw [if_pos hd] at ok
      have hw1 : callee w0 = w1 := Option.some.inj ok
      unfold plan at hp
      by_cases h0 : r.amount = 0
      · simp [h0] at hp
      · rw [if_neg h0] at hp
        by_cases hk : keys.dest = r.destination ∧ keys.vault = ids.vaultOf r.pool ∧
            keys.authority = ids.authorityOf r.pool ∧ keys.mint = ids.mintOf r.pool
        · rw [if_pos hk] at hp
          cases hv0 : w0 keys.vault with
          | none => simp [hv0] at hp
          | some v0 =>
            cases hd0 : w0 keys.dest with
            | none => simp [hv0, hd0] at hp
            | some d0 =>
              rw [hv0, hd0] at hp
              dsimp only at hp
              by_cases hc : v0.mint = keys.mint ∧ d0.mint = keys.mint ∧
                  v0.authority = keys.authority ∧ r.amount ≤ v0.amount
              · rw [if_pos hc] at hp
                have hpe := (Option.some.inj hp).symm
                subst hpe
                unfold DeltaOk at hd
                rw [rowA.1, rowA.2, hw1] at hd
                cases hv1 : w1 keys.vault with
                | none => simp [hv1] at hd
                | some v1 =>
                  cases hd1 : w1 keys.dest with
                  | none => simp [hv1, hd1] at hd
                  | some d1 =>
                    rw [hv1, hd1] at hd
                    obtain ⟨vm, dm, _, va, da⟩ := hd
                    have distinct : keys.vault ≠ keys.dest := by
                      intro same
                      rw [same] at hv0 hv1
                      rw [hv0] at hd0
                      rw [hv1] at hd1
                      have e0 := Option.some.inj hd0
                      have e1 := Option.some.inj hd1
                      subst e0; subst e1
                      simp only at va da
                      omega
                    refine ⟨Nat.pos_of_ne_zero h0, hk.1, hk.2.1, distinct,
                      ⟨v0, v1, hv0, hv1, ?_, ?_⟩, ⟨d0, d1, hd0, hd1, ?_, ?_⟩, ?_⟩
                    · simp only at va; omega
                    · simp only at vm; rw [vm, hk.2.2.2]
                    · simpa only using da
                    · simp only at dm; rw [dm, hk.2.2.2]
                    · intro k h1 h2
                      rw [← hw1]
                      exact rowB k h1 h2
              · rw [if_neg hc] at hp; simp at hp
        · rw [if_neg hk] at hp; simp at hp
    · rw [if_neg hd] at ok; simp at ok

/-! ### Composition with acceptance -/

/-- PayoutBound: an accepted withdrawal's settlement paid exactly the
statement's amount from the vault of the statement's pool to the statement's
destination token account, the statement's deployment being that pool's, and
changed no other account; `s` is the statement the verifier accepted a proof
bound to. Hypotheses:
* `rowA`, `rowB`: trust rows R-a, R-b (runtime class).
* `p1`: OPEN obligation, Aspis's request codec: decode after encode is the
  identity on the encoder's image (crates/aspis-statement/src/pool_v1/
  pair_forest_terminal.rs:432 encode, :466 decode).
* `e1`: OPEN obligation, the entry: the statement the verifier checks the
  proof against is `stmtOf` of the request it decoded (r1_pool_adapter_owned.rs
  one-transaction block of `stage2_owned`, `reconstruct_asq8_statement`), and
  `stmtOf` carries the request's pool, deployment, destination (iff
  withdrawal) and amount.
* `e1d`: OPEN obligation, the entry: it accepts only a statement whose
  deployment is its pool's (`authenticate_asq8_accounts`: master identity,
  checkpoint deployment). This is a condition on ACCEPTED statements only. In
  the first form of this theorem it was a conjunct of `e1`, quantified over
  every request; that hypothesis cannot hold (a request may name any
  deployment), so the first form was vacuous. `first_e1_form_unsatisfiable`
  below records the counterexample; `Witness.instance_paid` shows the present
  hypotheses hold together.
* `p3`: OPEN obligation, the Pool's call: the Pool sends the verifier
  `encode r` of the request it decoded (pair_forest_dispatch.rs:157, :342) and
  proceeds only if the verifier accepted (`accepted`) a proof bound to the
  statement built from the bytes it received.
* `p2`: OPEN obligation, the Pool's payout path computes `step` on that same
  request (vault.rs:387-580, pair_forest.rs around the withdrawal plan).
-/
theorem payout_bound (ids : PoolIds K)
    (encode : Request K → Option B) (decode : B → Option (Request K))
    (stmtOf : Request K → Statement K) (accepted : Statement K → Prop)
    (r : Request K) (keys : Keys K) (w0 w1 : World K)
    (callee : World K → World K) (read : World K → World K)
    -- trust rows
    (rowA : RowA keys callee read w0) (rowB : RowB keys callee w0)
    -- open obligations
    (p1 : ∀ q b, encode q = some b → decode b = some q)
    (e1 : ∀ q, (stmtOf q).pool = q.pool ∧ (stmtOf q).deployment = q.deployment ∧
      (stmtOf q).destination = (if q.withdrawal then some q.destination else none) ∧
      (stmtOf q).amount = q.amount)
    (e1d : ∀ s, accepted s → s.deployment = ids.deploymentOf s.pool)
    (p3 : ∃ b q', encode r = some b ∧ decode b = some q' ∧ accepted (stmtOf q'))
    (p2 : step ids r keys w0 callee read = some w1)
    (withdrawal : r.withdrawal = true) :
    ∃ s : Statement K, accepted s ∧
      s.destination = some keys.dest ∧
      keys.vault = ids.vaultOf s.pool ∧
      s.deployment = ids.deploymentOf s.pool ∧
      Paid ids r keys w0 w1 ∧ s.amount = r.amount := by
  obtain ⟨b, q', henc, hdec, hacc⟩ := p3
  have hq : q' = r := Option.some.inj ((hdec.symm).trans (p1 r b henc))
  subst hq
  have paid := step_paid ids q' keys w0 w1 callee read rowA rowB p2
  obtain ⟨hpool, _, hdest, hamt⟩ := e1 q'
  refine ⟨stmtOf q', hacc, ?_, ?_, e1d _ hacc, paid, hamt⟩
  · rw [hdest, withdrawal, if_pos rfl, paid.dest_eq]
  · rw [hpool]; exact paid.vault_eq

/-! ### The attempts to break it, as theorems -/

/-- A destination account other than the request's is rejected by the plan. -/
theorem wrong_destination_rejected (ids : PoolIds K) (r : Request K) (keys : Keys K)
    (w0 : World K) (callee : World K → World K) (read : World K → World K)
    (h : keys.dest ≠ r.destination) : step ids r keys w0 callee read = none := by
  unfold step plan
  by_cases h0 : r.amount = 0
  · simp [h0]
  · simp [h0, h]

/-- Amount 0 is rejected by the plan (vault.rs:398). -/
theorem zero_amount_rejected (ids : PoolIds K) (r : Request K) (keys : Keys K)
    (w0 : World K) (callee : World K → World K) (read : World K → World K)
    (h : r.amount = 0) : step ids r keys w0 callee read = none := by
  unfold step plan
  simp [h]

/-- The same account as vault and destination: no Ok step exists (the
post-call check would need `v - amount = v + amount` with a nonzero amount). -/
theorem same_account_rejected (ids : PoolIds K) (r : Request K) (keys : Keys K)
    (w0 w1 : World K) (callee : World K → World K) (read : World K → World K)
    (rowA : RowA keys callee read w0) (rowB : RowB keys callee w0)
    (h : keys.vault = keys.dest) : step ids r keys w0 callee read ≠ some w1 := by
  intro ok
  exact (step_paid ids r keys w0 w1 callee read rowA rowB ok).distinct h

/-- A callee that changes the vault's authority: no Ok step exists. -/
theorem authority_change_rejected (ids : PoolIds K) (r : Request K) (keys : Keys K)
    (w0 w1 : World K) (callee : World K → World K) (read : World K → World K)
    (rowA : RowA keys callee read w0)
    (v1 : TokenAccount K) (hv1 : callee w0 keys.vault = some v1)
    (h : v1.authority ≠ keys.authority) : step ids r keys w0 callee read ≠ some w1 := by
  intro ok
  unfold step at ok
  cases hp : plan ids r keys w0 with
  | none => simp [hp] at ok
  | some p =>
    rw [hp] at ok
    dsimp only at ok
    by_cases hd : DeltaOk p (read (callee w0))
    · have pk : p.keys = keys := by
        unfold plan at hp
        split at hp
        · simp at hp
        · split at hp
          · split at hp
            · split at hp
              · rw [← Option.some.inj hp]
              · simp at hp
            · simp at hp
          · simp at hp
      unfold DeltaOk at hd
      rw [pk, rowA.1, hv1] at hd
      split at hd
      · rename_i v d hv _
        have := Option.some.inj hv
        subst this
        exact h hd.2.2.1
      · exact hd
    · rw [if_neg hd] at ok; simp at ok

/-! ### The hypotheses hold together: a concrete instance

A theorem whose hypotheses cannot all hold says nothing. This section builds
one instance (addresses are numbers; an honest callee that does the exact
transfer) in which every hypothesis of `payout_bound` holds, and applies the
theorem to it. It is a satisfiability check of the hypotheses, not evidence
about the deployed programs. -/
namespace Witness

def ids : PoolIds Nat := ⟨fun p => p + 1, fun p => p + 2, fun p => p + 3, fun p => p + 4⟩
def r : Request Nat := ⟨10, 14, 50, 7, true⟩
def keys : Keys Nat := ⟨13, 11, 50, 12⟩
def w0 : World Nat := fun k =>
  if k = 11 then some ⟨13, 12, 100, 0⟩ else if k = 50 then some ⟨13, 99, 5, 0⟩ else none
/-- An honest token program: the exact transfer of 7 from account 11 to account 50. -/
def callee (w : World Nat) : World Nat := fun k =>
  if k = 11 then some ⟨13, 12, 93, 0⟩ else if k = 50 then some ⟨13, 99, 12, 0⟩ else w k
def stmtOf (q : Request Nat) : Statement Nat :=
  ⟨q.pool, q.deployment, if q.withdrawal then some q.destination else none, q.amount⟩
def accepted (s : Statement Nat) : Prop := s.deployment = s.pool + 4

theorem rowA : RowA keys callee id w0 := ⟨rfl, rfl⟩

theorem rowB : RowB keys callee w0 := by
  intro k h1 h2
  have h1' : k ≠ 11 := h1
  have h2' : k ≠ 50 := h2
  simp [callee, h1', h2']

theorem p1 : ∀ (q b : Request Nat), (some q : Option (Request Nat)) = some b → some b = some q :=
  fun _ _ h => h.symm

theorem e1 : ∀ q : Request Nat, (stmtOf q).pool = q.pool ∧ (stmtOf q).deployment = q.deployment ∧
    (stmtOf q).destination = (if q.withdrawal then some q.destination else none) ∧
    (stmtOf q).amount = q.amount := fun _ => ⟨rfl, rfl, rfl, rfl⟩

theorem e1d : ∀ s : Statement Nat, accepted s → s.deployment = ids.deploymentOf s.pool :=
  fun _ h => h

theorem p3 : ∃ (b q' : Request Nat), (some r : Option (Request Nat)) = some b ∧
    (some b : Option (Request Nat)) = some q' ∧ accepted (stmtOf q') :=
  ⟨r, r, rfl, rfl, by simp [accepted, stmtOf, r]⟩

theorem p2 : step ids r keys w0 callee id = some (callee w0) := by
  simp [step, plan, DeltaOk, ids, r, keys, w0, callee]

/-- `payout_bound` on the instance: all its hypotheses hold at once. -/
theorem instance_paid : ∃ s : Statement Nat, accepted s ∧ s.destination = some keys.dest ∧
    keys.vault = ids.vaultOf s.pool ∧ s.deployment = ids.deploymentOf s.pool ∧
    Paid ids r keys w0 (callee w0) ∧ s.amount = r.amount :=
  payout_bound ids some some stmtOf accepted r keys w0 (callee w0) callee id
    rowA rowB p1 e1 e1d p3 p2 rfl

/-- Retained counterexample. The first form of `payout_bound` asked, inside
`e1`, that EVERY request's deployment be its pool's. No such hypothesis holds
when a request can name a deployment freely: here request (pool 0,
deployment 0) against a pool whose deployment is 4. -/
theorem first_e1_form_unsatisfiable :
    ¬ ∀ q : Request Nat, q.deployment = ids.deploymentOf q.pool := by
  intro h
  have := h ⟨0, 0, 0, 0, false⟩
  simp [ids] at this

end Witness

#print axioms step_paid
#print axioms payout_bound
#print axioms Witness.instance_paid
#print axioms Witness.first_e1_form_unsatisfiable
#print axioms wrong_destination_rejected
#print axioms zero_amount_rejected
#print axioms same_account_rejected
#print axioms authority_change_rejected
end AspisPayout
end
