import FS.Theorem

/-! # Fiat–Shamir, v2: rounds as sampler programs — statement

v1 (`FS.Statement`) reads one oracle block per round at an `H`-independent
address.  The duplex of `AspisV8R19.DuplexFrames` derives a challenge by a
chain of adaptive reads (`absorb`, `squeeze`, `advance`, repeated squeezes),
and the tree's sampler laws are stated for sampler *programs*.  v2 therefore
lets round `i` produce its challenge by a program `samp i P m` that reads the
oracle itself.  Everything else is as in v1 and reused from it: prefixes,
tables, `firstReads`, `tableBefore`, `FirstReadsBound`, `maxErr`, (D1), (D3).

New objects:
* `follow s T tr`: run the sampler program `s` against a trace, consuming the
  cells it asks for at their first reads in order (`none` if a cell it asks for
  is already in the table or the trace ends first).
* (D2′): the density is `independentMean (samp i P m)` of the flip, i.e. the
  law of the sampler on fresh answers — the shape of R417/R601/R609/R945.
* (INJ): outside the collision event, the first cell of each transcript
  round's chain decodes to its prefix at the table of its first read, and the
  chain is then followed to completion (its cells are first-read in order).
* `Q_tot` is unchanged: distinct first reads of prover plus verifier. -/
set_option autoImplicit false
namespace FS2

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

/-! ## Following a sampler program along a trace -/

section Follow
variable {I A C : Type} [DecidableEq I]

/-- Run `s` against the trace from table `t`: cells `s` asks for must be
first reads, in order; other reads are skipped (and recorded). -/
def follow : Program I A C → Table I A → List (I × A) → Option C
  | .done c, _, _ => some c
  | .ask _ _, _, [] => none
  | .ask i k, t, (j, a) :: rest =>
      if j = i then (if t i = none then follow (k a) (put t i a) rest else none)
      else follow (.ask i k) (put t j a) rest

/-- The first cell a program asks for. -/
def firstCell : Program I A C → Option I
  | .done _ => none
  | .ask i _ => some i

end Follow

/-! ## Protocol -/

/-- §2 objects, v2.  Round `i` with prefix `P` and new message `m` derives
its challenge with the program `samp i P m`. -/
structure Protocol (X M C W Pf I A : Type) where
  r : Nat
  msg : Pf → Nat → M
  samp : Nat → Prefix X M C → M → Program I A C
  /-- decoding of a chain's first cell at the current table -/
  decode : I → Table I A → Option (Prefix X M C × M)
  extract : X → Table I A → Option W

namespace Protocol
variable {X M C W Pf I A : Type}

/-- Transcript prefixes: the challenge of round `i` is the sampler program's
output on the oracle. -/
def transcript (pr : Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    Nat → Prefix X M C
  | 0 => emptyPrefix x
  | i + 1 =>
      let P := pr.transcript H x π i
      P.ext (pr.msg π i) (eval H (pr.samp i P (pr.msg π i))).2

/-- Round `i`'s sampler program in the transcript. -/
def chain (pr : Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) (i : Nat) :
    Program I A C :=
  pr.samp i (pr.transcript H x π i) (pr.msg π i)

end Protocol

/-! ## Experiment and events -/

section Experiment
variable {X M C W Pf I A : Type} [DecidableEq I]

def experiment (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X) :
    Program I A (Pf × Bool) :=
  bind P (fun π => bind (V x π) (fun b => .done (π, b)))

def distinctFirstReads (v : View I A (Pf × Bool)) : Nat := firstReads emptyTable v.1

def accepts (v : View I A (Pf × Bool)) : Prop := v.2.2 = true

/-- The extractor fails on the table at the first read of the first cell of
the first round's chain (the address carrying the first message). -/
def extractFails (pr : Protocol X M C W Pf I A) (x : X) (v : View I A (Pf × Bool)) : Prop :=
  match firstCell (pr.samp 0 (emptyPrefix x) (pr.msg v.2.1 0)) with
  | some a => pr.extract x (tableBefore emptyTable v.1 a) = none
  | none => pr.extract x emptyTable = none

/-- Lemma A′'s event: some first read starts a decodable chain which is then
followed to completion with a bad output. -/
def hitsChain (bad : Prefix X M C → M → Table I A → C → Prop)
    (pr : Protocol X M C W Pf I A) : Table I A → List (I × A) → Prop
  | _, [] => False
  | t, (i, a) :: rest =>
      (t i = none ∧ ∃ (P : Prefix X M C) (m : M) (c : C), pr.decode i t = some (P, m) ∧
        follow (pr.samp P.round P m) t ((i, a) :: rest) = some c ∧ bad P m t c) ∨
      hitsChain bad pr (put t i a) rest

end Experiment

/-- §3 state predicate and errors (v1's shape, generic answer type). -/
structure RoundByRound' (X M C I A : Type) where
  doomed : Prefix X M C → Table I A → Prop
  ε : Nat → ℚ

/-! ## §3 hypotheses -/

section Hypotheses
variable {X M C W Pf I A : Type} [DecidableEq I] [Fintype A]

def D1 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A) : Prop :=
  ∀ (x : X) (T : Table I A), pr.extract x T = none → rb.doomed (emptyPrefix x) T

/-- (D2′) for every doomed prefix of round `i`, every next message and every
table `T`: the sampler's law on fresh answers gives the extension not doomed
at `T` with mass at most `ε_i`. -/
def D2 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A) : Prop :=
  ∀ (i : Nat) (P : Prefix X M C) (m : M) (T' T : Table I A),
    P.round = i → i < pr.r → rb.doomed P T' →
    independentMean (pr.samp i P m)
      (fun w => indicator (¬ rb.doomed (P.ext m w.2) T)) ≤ rb.ε i

def D3 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (V : X → Pf → Program I A Bool) : Prop :=
  ∀ (H : I → A) (x : X) (π : Pf) (T : Table I A),
    rb.doomed (pr.transcript H x π pr.r) T → (eval H (V x π)).2 = false

/-- §2 verifier: it reads the first cell of every round's chain. -/
def ReadsChains (pr : Protocol X M C W Pf I A) (V : X → Pf → Program I A Bool) : Prop :=
  ∀ (H : I → A) (x : X) (π : Pf) (i : Nat) (a : I), i < pr.r →
    firstCell (pr.chain H x π i) = some a → a ∈ (eval H (V x π)).1.map Prod.fst

end Hypotheses

/-- The trace from the first occurrence of address `a` (inclusive). -/
def traceFrom {I A : Type} [DecidableEq I] : List (I × A) → I → List (I × A)
  | [], _ => []
  | (i, b) :: rest, a => if i = a then (i, b) :: rest else traceFrom rest a

/-! ## (INJ) -/

section Inj
variable {X M C W Pf I A : Type} [DecidableEq I] [Fintype I] [Fintype A]

/-- (INJ), v2: a collision event of mass at most `κ(Q_tot)`; outside it, for
each round `i < r` whose chain reads at all, the chain's first cell decodes
at the table of its first read to the round's prefix and message, and the
chain is followed to completion from that first read. -/
structure Inj (pr : Protocol X M C W Pf I A) (P : Program I A Pf)
    (V : X → Pf → Program I A Bool) (x : X) (κ : Nat → ℚ) (Qtot : Nat) where
  Coll : View I A (Pf × Bool) → Prop
  mass : mean (fun H : I → A => indicator (Coll (eval H (experiment P V x)))) ≤ κ Qtot
  decodes : ∀ H : I → A, ¬ Coll (eval H (experiment P V x)) →
    ∀ i a, i < pr.r →
      let v := eval H (experiment P V x)
      firstCell (pr.chain H x v.2.1 i) = some a →
      pr.decode a (tableBefore emptyTable v.1 a) =
        some (pr.transcript H x v.2.1 i, pr.msg v.2.1 i)
  followed : ∀ H : I → A, ¬ Coll (eval H (experiment P V x)) →
    ∀ i a, i < pr.r →
      let v := eval H (experiment P V x)
      firstCell (pr.chain H x v.2.1 i) = some a →
      ∃ c, follow (pr.chain H x v.2.1 i) (tableBefore emptyTable v.1 a)
        (traceFrom v.1 a) = some c

end Inj

/-! ## Statements -/

section Statements
variable {X M C W Pf I A : Type} [DecidableEq I] [Fintype I] [Fintype A] [Nonempty A]

/-- The (D2′) bad-output family: a doomed prefix of some round `< r` whose
extension by the chain's output is not doomed at the current table. -/
def d2Bad (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Prefix X M C) (m : M) (T : Table I A) (c : C) : Prop :=
  P.round < pr.r ∧ (∃ T', rb.doomed P T') ∧ ¬ rb.doomed (P.ext m c) T

/-- §4, v2. -/
def Theorem4 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Prop :=
  D1 pr rb → D2 pr rb → D3 pr rb V → ReadsChains pr V →
  Inj pr P V x κ Qtot →
  (∀ H, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot) →
  mean (fun H : I → A =>
      indicator (accepts (eval H (experiment P V x)) ∧ extractFails pr x (eval H (experiment P V x)))) ≤
    (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot

/-- Lemma B′. -/
def LemmaB (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Prop :=
  D1 pr rb → D2 pr rb → D3 pr rb V → ReadsChains pr V →
  ∀ (inj : Inj pr P V x κ Qtot) (H : I → A),
    ¬ inj.Coll (eval H (experiment P V x)) →
    accepts (eval H (experiment P V x)) → extractFails pr x (eval H (experiment P V x)) →
    hitsChain (d2Bad pr rb) pr emptyTable (eval H (experiment P V x)).1

end Statements

/-- The embedded-chain lemma: in any continuation program, the mass of
"`s`'s cells are first-read in order and its output is bad" is at most the
sampler's own law on fresh answers. -/
def ChainLemma : Prop :=
  ∀ {I A C O : Type} [DecidableEq I] [Fintype A] [Nonempty A]
    (q : Program I A O) (t : Table I A) (s : Program I A C) (bad : C → Prop),
    lazyMean q t (fun v => indicator (∃ c, follow s t v.1 = some c ∧ bad c)) ≤
      independentMean s (fun w => indicator (bad w.2))

/-- Lemma A′: union bound over first reads that start a decodable chain. -/
def LemmaA : Prop :=
  ∀ {X M C W Pf I A : Type} [DecidableEq I] [Fintype A] [Nonempty A]
    (pr : Protocol X M C W Pf I A) (bad : Prefix X M C → M → Table I A → C → Prop)
    (ε : ℚ) (q : Program I A (Pf × Bool)) (t : Table I A) (N : Nat),
    0 ≤ ε →
    (∀ (P : Prefix X M C) (m : M) (T : Table I A),
      independentMean (pr.samp P.round P m) (fun w => indicator (bad P m T w.2)) ≤ ε) →
    FirstReadsBound q t N →
    lazyMean q t (fun v => indicator (hitsChain bad pr t v.1)) ≤ (N : ℚ) * ε

end FS2
