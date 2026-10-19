import AspisV8R19.AdaptiveFirstReadLaw
import AspisV8R19.CausalFirstHitUnionBound

/-! # Fiat–Shamir for a round-by-round sound protocol: statement

Definitions and statements only, following `FS_GENERIC.md` §2–§5.  No proofs
appear in this file.  The oracle model is the existing memoised one
(`Program`, `Table`, `lazyMean`, `eval`); nothing from it is duplicated.

Representation decisions (§6 leaves these to the formaliser):

* The oracle answers one *block* per address, `Fin K → B`, where `B` is the
  base answer (256 bits) and `K` bounds every round's `k_i`.  Round `i`'s
  sampler is a function of the first `k_i` base answers of the block read at
  the round's address; the block is the "fresh answer tuple" of a first read.
* A prefix of §3 (the argument of `doomed`) is challenge-ending:
  `(x, (m_1,c_1), …, (m_i,c_i))`; the empty prefix is `(x, [])`.  A prefix of
  §2 (the argument of `addr`) is such a prefix followed by the next message.
  Round indices are 0-based: the challenge appended to a prefix with `i`
  completed rounds uses `sampler i`, `k i`, `ε i`.
* The address interface is `addr` (prefix → address) together with `decode`
  (address, current table → prefix).  (INJ) is stated as the collision event
  plus its deterministic content: outside the event every transcript prefix's
  address decodes to that prefix at the table of its first read.
* "Doomed prefix" in (D2)/(D3) is read as "doomed with respect to some table"
  and the extension's doomedness is evaluated at the quantified table, as the
  text's quantifier order says.
-/
set_option autoImplicit false
namespace FS

open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

/-! ## Memoised-oracle bookkeeping -/

section Oracle
variable {I A : Type} [DecidableEq I]

/-- Number of first reads (cache misses) along a trace started at table `t`.
A re-read of an address already in the table is a cache hit and counts 0. -/
def firstReads (t : Table I A) : List (I × A) → Nat
  | [] => 0
  | (i, a) :: rest => (if t i = none then 1 else 0) + firstReads (put t i a) rest

/-- The table immediately before the first read of `j` in a trace started at
`t` (the final table if `j` is never read). -/
def tableBefore (t : Table I A) : List (I × A) → I → Table I A
  | [], _ => t
  | (i, a) :: rest, j => if i = j then t else tableBefore (put t i a) rest j

/-- Some first read of the trace, started at table `t`, lands in its bad set
`bad address table answer`. -/
def hitsBad (bad : I → Table I A → A → Prop) : Table I A → List (I × A) → Prop
  | _, [] => False
  | t, (i, a) :: rest => (t i = none ∧ bad i t a) ∨ hitsBad bad (put t i a) rest

/-- Empty table. -/
def emptyTable : Table I A := fun _ => none

end Oracle

/-- Along every execution path from table `t` the program makes at most `n`
first reads (cache misses). -/
def FirstReadsBound {I A O : Type} [DecidableEq I] :
    Program I A O → Table I A → Nat → Prop
  | .done _, _, _ => True
  | .ask i next, t, n =>
      match t i with
      | some a => FirstReadsBound (next a) t n
      | none => 0 < n ∧ ∀ a, FirstReadsBound (next a) (put t i a) (n - 1)

/-! ## Prefixes, samplers, protocol -/

/-- Challenge-ending prefix `(x, (m_1,c_1), …, (m_i,c_i))`; `rounds = []` is
the empty prefix. -/
structure Prefix (X M C : Type) where
  statement : X
  rounds : List (M × C)

namespace Prefix
variable {X M C : Type}
def round (P : Prefix X M C) : Nat := P.rounds.length
def ext (P : Prefix X M C) (m : M) (c : C) : Prefix X M C :=
  ⟨P.statement, P.rounds ++ [(m, c)]⟩
end Prefix

def emptyPrefix {X M C : Type} (x : X) : Prefix X M C := ⟨x, []⟩

/-- Oracle block answer: `K` base answers read at one address. -/
abbrev Block (B : Type) (K : Nat) := Fin K → B

/-- The first `k` base answers of a block. -/
def restrict {B : Type} {K k : Nat} (h : k ≤ K) (b : Block B K) : Fin k → B :=
  fun j => b (Fin.castLE h j)

/-- §2 objects.  `X` statements, `M` messages, `C` challenges, `W` witnesses,
`Pf` proofs, `I` addresses, `B` base answers, `K` block width. -/
structure Protocol (X M C W Pf I B : Type) (K : Nat) where
  /-- number of challenge rounds `r` -/
  r : Nat
  /-- messages `m_1, …, m_{r+1}` of a proof, 0-based; `msg π r` is the final message -/
  msg : Pf → Nat → M
  /-- `k_i`: base answers consumed by round `i`'s sampler -/
  k : Nat → Nat
  hk : ∀ i, k i ≤ K
  /-- sampler `σ_i`, a function of the `k_i` fresh answers -/
  sampler : (i : Nat) → (Fin (k i) → B) → C
  /-- address map on message-ending prefixes -/
  addr : Prefix X M C → M → I
  /-- decoding of an address at the current table -/
  decode : I → Table I (Block B K) → Option (Prefix X M C × M)
  /-- extractor: a function of the statement and the table at first read -/
  extract : X → Table I (Block B K) → Option W

/-- §3 objects: the state predicate on (prefix, table) and the round errors. -/
structure RoundByRound (X M C I B : Type) (K : Nat) where
  doomed : Prefix X M C → Table I (Block B K) → Prop
  ε : Nat → ℚ

namespace Protocol
variable {X M C W Pf I B : Type} {K : Nat}

/-- Challenge of round `i` from the block read at the round's address. -/
def chal (pr : Protocol X M C W Pf I B K) (i : Nat) (b : Block B K) : C :=
  pr.sampler i (restrict (pr.hk i) b)

/-- The transcript's challenge-ending prefixes determined by the oracle and the
proof: `transcript H x π i` is the prefix of round `i`, with each challenge the
sampler of the oracle block at the address of the preceding message-ending
prefix. -/
def transcript (pr : Protocol X M C W Pf I B K) (H : I → Block B K) (x : X) (π : Pf) :
    Nat → Prefix X M C
  | 0 => emptyPrefix x
  | i + 1 =>
      let P := pr.transcript H x π i
      P.ext (pr.msg π i) (pr.chal i (H (pr.addr P (pr.msg π i))))

/-- Address read for the challenge of round `i` (0-based) of the transcript. -/
def chalAddr (pr : Protocol X M C W Pf I B K) (H : I → Block B K) (x : X) (π : Pf)
    (i : Nat) : I :=
  pr.addr (pr.transcript H x π i) (pr.msg π i)

end Protocol

/-! ## Experiment: prover then verifier on one memoised oracle -/

section Experiment
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I]

/-- The prover runs, then the verifier on its output; both read the same
oracle.  The verifier's re-reads of prover addresses are cache hits. -/
def experiment (P : Program I (Block B K) Pf) (V : X → Pf → Program I (Block B K) Bool)
    (x : X) : Program I (Block B K) (Pf × Bool) :=
  bind P (fun π => bind (V x π) (fun b => .done (π, b)))

/-- `Q_tot`: the number of distinct first-read addresses of prover plus
verifier along the trace. -/
def distinctFirstReads (v : View I (Block B K) (Pf × Bool)) : Nat :=
  firstReads emptyTable v.1

def accepts (v : View I (Block B K) (Pf × Bool)) : Prop := v.2.2 = true

/-- The extractor fails on the table at the first read of the address carrying
the first message (§2 extraction). -/
def extractFails (pr : Protocol X M C W Pf I B K) (x : X)
    (v : View I (Block B K) (Pf × Bool)) : Prop :=
  pr.extract x (tableBefore emptyTable v.1 (pr.addr (emptyPrefix x) (pr.msg v.2.1 0))) = none

end Experiment

/-! ## §3 hypotheses -/

section Hypotheses
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I] [Fintype B]

/-- (D1) the empty prefix is doomed when the extractor finds no witness for `x`
in the table. -/
def D1 (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K) : Prop :=
  ∀ (x : X) (T : Table I (Block B K)), pr.extract x T = none → rb.doomed (emptyPrefix x) T

/-- (D2) for every doomed prefix of round `i`, every next message and every
table `T`: the fraction of fresh answer tuples `a ∈ B^{k_i}` for which the
extended prefix is not doomed at `T` is at most `ε_i`. -/
def D2 (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K) : Prop :=
  ∀ (i : Nat) (P : Prefix X M C) (m : M) (T' T : Table I (Block B K)),
    P.round = i → i < pr.r → rb.doomed P T' →
    mean (fun a : Fin (pr.k i) → B =>
      indicator (¬ rb.doomed (P.ext m (pr.sampler i a)) T)) ≤ rb.ε i

/-- (D3) a doomed complete transcript is rejected by `V`.  The complete
transcript is the round-`r` prefix followed by the final message; it is doomed
when that prefix is. -/
def D3 (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K)
    (V : X → Pf → Program I (Block B K) Bool) : Prop :=
  ∀ (H : I → Block B K) (x : X) (π : Pf) (T : Table I (Block B K)),
    rb.doomed (pr.transcript H x π pr.r) T → (eval H (V x π)).2 = false

/-- §2 verifier: it re-reads every challenge address. -/
def ReadsChallenges (pr : Protocol X M C W Pf I B K)
    (V : X → Pf → Program I (Block B K) Bool) : Prop :=
  ∀ (H : I → Block B K) (x : X) (π : Pf) (i : Nat), i < pr.r →
    pr.chalAddr H x π i ∈ (eval H (V x π)).1.map Prod.fst

end Hypotheses

/-! ## (INJ) -/

section Inj
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I] [Fintype I] [Fintype B]

/-- (INJ): a collision event of mass at most `κ(Q_tot)`, outside of which the
address of each transcript prefix decodes, at the table of its first read, to
that prefix. -/
structure Inj (pr : Protocol X M C W Pf I B K) (P : Program I (Block B K) Pf)
    (V : X → Pf → Program I (Block B K) Bool) (x : X) (κ : Nat → ℚ) (Qtot : Nat) where
  Coll : View I (Block B K) (Pf × Bool) → Prop
  mass : mean (fun H : I → Block B K => indicator (Coll (eval H (experiment P V x)))) ≤ κ Qtot
  decodes : ∀ H : I → Block B K, ¬ Coll (eval H (experiment P V x)) →
    ∀ i, i < pr.r →
      let v := eval H (experiment P V x)
      let a := pr.chalAddr H x v.2.1 i
      pr.decode a (tableBefore emptyTable v.1 a) =
        some (pr.transcript H x v.2.1 i, pr.msg v.2.1 i)

end Inj

/-! ## §4 theorem and §5 lemmas as propositions -/

/-- `max_i ε_i` over the rounds `i < r` (and `0`). -/
def maxErr (ε : Nat → ℚ) (r : Nat) : ℚ :=
  (List.range r).foldr (fun i m => max (ε i) m) 0

section Statements
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I] [Fintype I] [Fintype B] [Nonempty B]

/-- The bad-set family of (D2), indexed by address and current table: the
address decodes to a doomed prefix of some round `i < r` and the block's
challenge extends it to a prefix that is not doomed at the current table. -/
def d2Bad (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K)
    (a : I) (T : Table I (Block B K)) (b : Block B K) : Prop :=
  ∃ (P : Prefix X M C) (m : M), pr.decode a T = some (P, m) ∧ P.round < pr.r ∧
    (∃ T', rb.doomed P T') ∧ ¬ rb.doomed (P.ext m (pr.chal P.round b)) T

/-- §4: `Pr_H[V^H(x, P^H) = 1 ∧ extractor fails] ≤ Q_tot · max_i ε_i + κ(Q_tot)`. -/
def Theorem4 (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K)
    (P : Program I (Block B K) Pf) (V : X → Pf → Program I (Block B K) Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Prop :=
  D1 pr rb → D2 pr rb → D3 pr rb V → ReadsChallenges pr V →
  Inj pr P V x κ Qtot →
  (∀ H, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot) →
  mean (fun H : I → Block B K =>
      indicator (accepts (eval H (experiment P V x)) ∧ extractFails pr x (eval H (experiment P V x)))) ≤
    (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot

/-- Lemma B (deterministic inclusion): outside the collision event, acceptance
with a failed extractor puts some first read in the (D2) bad set. -/
def LemmaB (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K)
    (P : Program I (Block B K) Pf) (V : X → Pf → Program I (Block B K) Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Prop :=
  D1 pr rb → D3 pr rb V → ReadsChallenges pr V →
  ∀ (inj : Inj pr P V x κ Qtot) (H : I → Block B K),
    ¬ inj.Coll (eval H (experiment P V x)) →
    accepts (eval H (experiment P V x)) → extractFails pr x (eval H (experiment P V x)) →
    hitsBad (d2Bad pr rb) emptyTable (eval H (experiment P V x)).1

end Statements

/-- Lemma A (first-read union bound): for a memoised program with at most `N`
first reads from table `t`, and bad sets of density at most `ε` over the fresh
answer, the probability that some first read lands in its bad set is at most
`N·ε`.  Addresses and stopping are adaptive; cache hits are not charged. -/
def LemmaA : Prop :=
  ∀ {I A O : Type} [DecidableEq I] [Fintype A] [Nonempty A]
    (p : Program I A O) (t : Table I A) (N : Nat)
    (bad : I → Table I A → A → Prop) (ε : ℚ),
    0 ≤ ε →
    (∀ (i : I) (t : Table I A), mean (fun a => indicator (bad i t a)) ≤ ε) →
    FirstReadsBound p t N →
    lazyMean p t (fun v => indicator (hitsBad bad t v.1)) ≤ (N : ℚ) * ε

end FS
