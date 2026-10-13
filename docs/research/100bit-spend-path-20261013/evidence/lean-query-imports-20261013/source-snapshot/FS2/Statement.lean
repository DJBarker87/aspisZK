import FS.Theorem

/-! # Fiat–Shamir, v2: rounds as sampler programs — statement

v1 (`FS.Statement`) reads one oracle block per round at an `H`-independent
address.  The duplex of `AspisV8R19.DuplexFrames` derives a challenge by a
chain of adaptive reads (`absorb`, then `squeeze` and `advance` of the
absorbed state in either order), and the tree's sampler laws are stated for
sampler programs.  Moreover a prover may absorb the next message before
reading the current challenge, so when a round's chain starts some earlier
challenge cells can still be unread; the round's flip then depends on cells
read later.  v2 therefore:

* lets round `i` derive its challenge by a sampler program `samp i P m`
  (`Sampler`: single reads, and `multi` — a set of determined cells read in
  any order);
* lets `decode a T` return the *completing sampler* of the round starting at
  the first read of `a`: it reads `a`, the round's remaining cells and any
  earlier challenge cells still missing from `T`, and outputs the completed
  prefix, the message and the new challenge;
* charges, per first read, the completing sampler's law on fresh answers
  (`ChainDensity`); an instantiation derives it from (D2) by averaging over
  the late cells.

Everything else is as in v1 and reused from it: prefixes, tables,
`firstReads`, `tableBefore`, `FirstReadsBound`, `maxErr`, (D1), (D3). -/
set_option autoImplicit false
namespace FS2

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

/-! ## Sampler programs -/

/-- A sampler program: single reads, and `multi c cs k`, a nonempty duplicate-
free set of cells whose addresses are all determined, read in any order; the
continuation receives the answers as a function on addresses. -/
inductive Sampler (I A C : Type)
  | done (c : C)
  | ask (i : I) (k : A → Sampler I A C)
  | multi (c : I) (cs : List I) (nd : (c :: cs).Nodup) (k : (I → A) → Sampler I A C)

section Follow
variable {I A C : Type} [DecidableEq I] [Inhabited A]

/-- Read a list of cells in order, accumulating answers. -/
def multiProg : List I → ((I → A) → Program I A C) → Program I A C
  | [], f => f default
  | c :: cs, f => .ask c fun a => multiProg cs (fun acc => f (Function.update acc c a))

/-- The ordinary program that runs a sampler (a `multi` read in list order). -/
def Sampler.toProgram : Sampler I A C → Program I A C
  | .done c => .done c
  | .ask i k => .ask i fun a => (k a).toProgram
  | .multi c cs _ k => multiProg (c :: cs) (fun acc => (k acc).toProgram)

/-- Consume one cell of a `multi`. -/
def stepMulti (c : I) (cs : List I) (nd : (c :: cs).Nodup) (k : (I → A) → Sampler I A C)
    (l : I) (a : A) : Sampler I A C :=
  match h : (c :: cs).erase l with
  | [] => k (Function.update default l a)
  | c' :: cs' => .multi c' cs' (h ▸ nd.erase l) (fun acc => k (Function.update acc l a))

/-- Run `s` against the trace from table `t`: cells `s` asks for must be
first reads, in the sampler's order except that the cells of a `multi` may
come in any order; other reads are skipped (and recorded). -/
def follow : Sampler I A C → Table I A → List (I × A) → Option C
  | .done c, _, _ => some c
  | .ask _ _, _, [] => none
  | .multi _ _ _ _, _, [] => none
  | .ask i k, t, (l, a) :: rest =>
      if l = i then (if t i = none then follow (k a) (put t i a) rest else none)
      else follow (.ask i k) (put t l a) rest
  | .multi c cs nd k, t, (l, a) :: rest =>
      if l ∈ c :: cs then
        (if t l = none then follow (stepMulti c cs nd k l a) (put t l a) rest else none)
      else follow (.multi c cs nd k) (put t l a) rest

/-- The first cell a sampler asks for. -/
def firstCell : Sampler I A C → Option I
  | .done _ => none
  | .ask i _ => some i
  | .multi c _ _ _ => some c

end Follow

/-! ## Protocol -/

/-- §2 objects, v2.  Round `i` with prefix `P` and new message `m` derives
its challenge with `samp i P m`; `decode a T` is the completing sampler of
the round whose chain starts at a first read of `a` with table `T`. -/
structure Protocol (X M C W Pf I A : Type) where
  r : Nat
  msg : Pf → Nat → M
  samp : Nat → Prefix X M C → M → Sampler I A C
  decode : I → Table I A → Option (Sampler I A (Prefix X M C × M × C))
  extract : X → Table I A → Option W

namespace Protocol
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]

/-- Transcript prefixes: the challenge of round `i` is the sampler program's
output on the oracle. -/
def transcript (pr : Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    Nat → Prefix X M C
  | 0 => emptyPrefix x
  | i + 1 =>
      let P := pr.transcript H x π i
      P.ext (pr.msg π i) (eval H (pr.samp i P (pr.msg π i)).toProgram).2

/-- Round `i`'s sampler program in the transcript. -/
def chain (pr : Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) (i : Nat) :
    Sampler I A C :=
  pr.samp i (pr.transcript H x π i) (pr.msg π i)

/-- Round `i`'s challenge in the transcript. -/
def chal (pr : Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) (i : Nat) : C :=
  (eval H (pr.chain H x π i).toProgram).2

end Protocol

/-! ## Experiment and events -/

section Experiment
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]

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

/-- Lemma A′'s event: some first read decodes to a completing sampler which
is followed to completion with a bad output. -/
def hitsChain (bad : Prefix X M C → M → Table I A → C → Prop)
    (pr : Protocol X M C W Pf I A) : Table I A → List (I × A) → Prop
  | _, [] => False
  | t, (i, a) :: rest =>
      (t i = none ∧ ∃ (S : Sampler I A (Prefix X M C × M × C)) (P : Prefix X M C) (m : M) (c : C),
        pr.decode i t = some S ∧ follow S t ((i, a) :: rest) = some (P, m, c) ∧ bad P m t c) ∨
      hitsChain bad pr (put t i a) rest

/-- The trace from the first occurrence of address `a` (inclusive). -/
def traceFrom : List (I × A) → I → List (I × A)
  | [], _ => []
  | (i, b) :: rest, a => if i = a then (i, b) :: rest else traceFrom rest a

end Experiment

/-- §3 state predicate and errors (v1's shape, generic answer type). -/
structure RoundByRound' (X M C I A : Type) where
  doomed : Prefix X M C → Table I A → Prop
  ε : Nat → ℚ

/-! ## §3 hypotheses -/

section Hypotheses
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A] [Fintype A]

def D1 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A) : Prop :=
  ∀ (x : X) (T : Table I A), pr.extract x T = none → rb.doomed (emptyPrefix x) T

/-- (D2′) for every doomed prefix of round `i`, every next message and every
table `T`: the sampler's law on fresh answers gives the extension not doomed
at `T` with mass at most `ε_i`. -/
def D2 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A) : Prop :=
  ∀ (i : Nat) (P : Prefix X M C) (m : M) (T' T : Table I A),
    P.round = i → i < pr.r → rb.doomed P T' →
    independentMean (pr.samp i P m).toProgram
      (fun w => indicator (¬ rb.doomed (P.ext m w.2) T)) ≤ rb.ε i

/-- The (D2′) bad-output family: a doomed prefix of some round `< r` whose
extension by the chain's output is not doomed at the current table. -/
def d2Bad (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Prefix X M C) (m : M) (T : Table I A) (c : C) : Prop :=
  P.round < pr.r ∧ (∃ T', rb.doomed P T') ∧ ¬ rb.doomed (P.ext m c) T

/-- The per-first-read charge: every completing sampler `decode` can return
has flip mass at most `max_i ε_i` on fresh answers.  Derived from (D2′) by
an instantiation (averaging over the late cells). -/
def ChainDensity (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A) : Prop :=
  ∀ (a : I) (T : Table I A) (S : Sampler I A (Prefix X M C × M × C)),
    pr.decode a T = some S →
    independentMean S.toProgram
      (fun w => indicator (d2Bad pr rb w.2.1 w.2.2.1 T w.2.2.2)) ≤ maxErr rb.ε pr.r

def D3 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (V : X → Pf → Program I A Bool) : Prop :=
  ∀ (H : I → A) (x : X) (π : Pf) (T : Table I A),
    rb.doomed (pr.transcript H x π pr.r) T → (eval H (V x π)).2 = false

/-- Every round's sampler reads the oracle (a round with a deterministic
challenge has no first read to charge). -/
def ChainsRead (pr : Protocol X M C W Pf I A) : Prop :=
  ∀ (i : Nat) (P : Prefix X M C) (m : M), i < pr.r → firstCell (pr.samp i P m) ≠ none

/-- §2 verifier: it reads the first cell of every round's chain. -/
def ReadsChains (pr : Protocol X M C W Pf I A) (V : X → Pf → Program I A Bool) : Prop :=
  ∀ (H : I → A) (x : X) (π : Pf) (i : Nat) (a : I), i < pr.r →
    firstCell (pr.chain H x π i) = some a → a ∈ (eval H (V x π)).1.map Prod.fst

end Hypotheses

/-! ## (INJ) -/

section Inj
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A] [Fintype I] [Fintype A]

/-- (INJ), v2: a collision event of mass at most `κ(Q_tot)`; outside it, for
each round `i < r`, the first cell of the round's chain decodes, at the table
of its first read, to a completing sampler that is followed to completion
from that read and outputs the round's prefix, message and challenge. -/
structure Inj (pr : Protocol X M C W Pf I A) (P : Program I A Pf)
    (V : X → Pf → Program I A Bool) (x : X) (κ : Nat → ℚ) (Qtot : Nat) where
  Coll : View I A (Pf × Bool) → Prop
  mass : mean (fun H : I → A => indicator (Coll (eval H (experiment P V x)))) ≤ κ Qtot
  decodes : ∀ H : I → A, ¬ Coll (eval H (experiment P V x)) →
    ∀ i a, i < pr.r →
      let v := eval H (experiment P V x)
      firstCell (pr.chain H x v.2.1 i) = some a →
      ∃ S, pr.decode a (tableBefore emptyTable v.1 a) = some S ∧
        follow S (tableBefore emptyTable v.1 a) (traceFrom v.1 a) =
          some (pr.transcript H x v.2.1 i, pr.msg v.2.1 i, pr.chal H x v.2.1 i)

end Inj

/-! ## Statements -/

section Statements
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A] [Fintype I] [Fintype A] [Nonempty A]

/-- §4, v2. -/
def Theorem4 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Prop :=
  D1 pr rb → ChainDensity pr rb → D3 pr rb V → ChainsRead pr → ReadsChains pr V →
  Inj pr P V x κ Qtot →
  (∀ H, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot) →
  mean (fun H : I → A =>
      indicator (accepts (eval H (experiment P V x)) ∧ extractFails pr x (eval H (experiment P V x)))) ≤
    (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot

/-- Lemma B′. -/
def LemmaB (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Prop :=
  D1 pr rb → D3 pr rb V → ChainsRead pr → ReadsChains pr V →
  ∀ (inj : Inj pr P V x κ Qtot) (H : I → A),
    ¬ inj.Coll (eval H (experiment P V x)) →
    accepts (eval H (experiment P V x)) → extractFails pr x (eval H (experiment P V x)) →
    hitsChain (d2Bad pr rb) pr emptyTable (eval H (experiment P V x)).1

end Statements

/-- The embedded-chain lemma: in any continuation program, the mass of
"`s`'s cells are first-read (in any admissible order) and its output is bad"
is at most the sampler's own law on fresh answers. -/
def ChainLemma : Prop :=
  ∀ {I A C O : Type} [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]
    (q : Program I A O) (t : Table I A) (s : Sampler I A C) (bad : C → Prop),
    lazyMean q t (fun v => indicator (∃ c, follow s t v.1 = some c ∧ bad c)) ≤
      independentMean s.toProgram (fun w => indicator (bad w.2))

/-- Lemma A′: union bound over first reads that decode to a completing
sampler. -/
def LemmaA : Prop :=
  ∀ {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]
    (pr : Protocol X M C W Pf I A) (bad : Prefix X M C → M → Table I A → C → Prop)
    (ε : ℚ) (q : Program I A (Pf × Bool)) (t : Table I A) (N : Nat),
    0 ≤ ε →
    (∀ (a : I) (T : Table I A) (S : Sampler I A (Prefix X M C × M × C)), pr.decode a T = some S →
      independentMean S.toProgram (fun w => indicator (bad w.2.1 w.2.2.1 T w.2.2.2)) ≤ ε) →
    FirstReadsBound q t N →
    lazyMean q t (fun v => indicator (hitsChain bad pr t v.1)) ≤ (N : ℚ) * ε

end FS2
