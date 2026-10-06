# Generic Fiat–Shamir theorem: formalisation log

2026-10-06. Formalises `docs/research/v8-wide-reference-20261005/FS_GENERIC.md`
(branch `research/v8-wide-reference-20261005`, spec revision `c5f6ce529`).
Sources: `lean/FS/{Statement,LemmaA,LemmaB,Theorem}.lean`. Nothing outside
this directory was changed.

## Result

- `FS.theorem4 : Theorem4 …` — the §4 inequality
  `Pr_H[V accepts ∧ extractor fails] ≤ Q_tot · max_i ε_i + κ(Q_tot)`,
  proved from (D1)–(D3), the §2 verifier property (re-reads challenge
  addresses), (INJ) and the `Q_tot` bound. `κ(Q_tot)` is an explicit summand;
  the per-read charge is `maxErr ε r = max_{i<r} ε_i` (seed 0), not the sum.
- `FS.lemmaA : LemmaA` — first-read union bound over the existing `Program`
  type with adaptive addresses and stopping; cache hits are not charged.
- `FS.lemmaB : LemmaB …` — deterministic inclusion exactly as §5: first round
  where doomedness flips; that round's address was read (verifier) and decodes
  to its prefix at the table of its first read; the fresh block there lies in
  the (D2) bad set.
- All `#print axioms`: `propext, Classical.choice, Quot.sound` only. No
  `sorry`, `axiom`, `native_decide`, `admit` in the sources (grep verified).
- Not instantiated for R0, V7 or any protocol.

## Environment

- Host `nuc` (dombarker@100.108.41.90), Lean `leanprover/lean4:v4.32.0`,
  binary `~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`.
- Pinned workspace for Mathlib and dependency objects:
  `/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal`
  (`lake env` captured once into `evidence/environment-base.json`; Lake exits
  before Lean starts).
- Work directory `/home/dombarker/project-offloads/aspis-fs-generic-20261006/`
  (`sources/`, `objects/`, `evidence/`; nothing there is committed).
- `LEAN_PATH` = `objects` : captured Lake `LEAN_PATH` (Cli, batteries, Qq,
  aesop, proofwidgets, importGraph, LeanSearchClient, plausible, mathlib, the
  workspace build lib, the toolchain lib). `objects/` holds symlinks
  `AspisV8R19`, `AspisV8R17`, `AspisV8Privacy`, `AspisV8PairedCommitment` →
  `aspis-r126-release-20260930-a/lib/<root>` and the real directory `FS/`.
  The mirror is first because the workspace build lib also contains a stale
  `AspisV8R19`/`AspisV8R17` root lacking the needed modules (CONVERGENCE §5
  duplicate-root hazard). The audit lib was not needed: all eight imported
  modules (`AspisV8Privacy.FiniteGames`, `AspisV8R17.AdaptiveOracle`,
  `AspisV8R19.{OracleResampling, MemoizedProgramLaw, OracleProgramOps,
  AdaptiveFirstReadLaw, CausalFirstHitUnionBound}`,
  `AspisV8PairedCommitment.Table`) are in the r126 lib, byte-identical to the
  audit copies where both exist.
- Command per file (`run.sh`): one `systemd-run --user --scope` with
  `MemoryHigh=5G MemoryMax=7G MemorySwapMax=0 TasksMax=128`, GNU
  `/usr/bin/time -v`, `timeout 900`,
  `lean -j1 -M4500 -DElab.async=false -R sources -o objects/FS/X.olean sources/FS/X.lean`.
  One Lean job at a time; no other Aspis scope was active (host had ≈46 GB
  available at each launch).
- Import footprint probe (attempt 000, imports only + one `#print axioms`):
  exit 0, 1.33 s, peak RSS 3,299,144 KiB, 0 swaps. `-M4500` kept throughout;
  no cap was ever raised.
- A local Mac compile of the eight dependency modules into the session
  scratchpad was started before the instruction to use the NUC only; it
  finished (all exit 0) and was not used for any recorded result. No local
  `lake build`; `/Users/dominic/ZK/AspisFormal` untouched.

## Per-file record (final clean replay, attempts 010–013, objects removed first)

Source revision: branch at `4e7a0b060` (Statement commit) + the three proof
files; SHA-256 of the committed sources below.

| Target | SHA-256 | exit | wall | peak RSS KiB | swaps | `#print axioms` |
|---|---|---:|---:|---:|---:|---|
| `lean/FS/Statement.lean` | `7251b37e0302e26dd40bd05cc60665c884b5899e1e96e3b5c9402404b2e6bd78` | 0 | 1.91 s | 3,332,788 | 0 | no theorems (definitions and Props only) |
| `lean/FS/LemmaA.lean` | `9e27ba25a01bc6c4e7a88c592a897f509da89fb42c7b3d9a6a0c3e7371d4895d` | 0 | 2.21 s | 3,339,960 | 0 | `lemmaA`: propext, Classical.choice, Quot.sound |
| `lean/FS/LemmaB.lean` | `cd1d4d4fa3d499a4dbd58f65840b4d020f40b9c3900a45a4124fd37c7a72ca52` | 0 | 1.84 s | 3,327,436 | 0 | `lemmaB`: propext, Classical.choice, Quot.sound |
| `lean/FS/Theorem.lean` | `bebe53c889055578756a98efacf699e9d671de511459ce4215329e882859530e` | 0 | 1.87 s | 3,334,524 | 0 | `theorem4`, `lemmaA`, `lemmaB`: propext, Classical.choice, Quot.sound |

## Attempts

| # | target | outcome |
|---|---|---|
| 000 | imports probe | exit 0 (footprint) |
| 001 | Statement | exit 0 (committed alone as `4e7a0b060`) |
| 002 | LemmaA | exit 1: `indicator_mono` negative case unsolved (`lemmaA` itself already P/C/Q) |
| 003 | LemmaA | exit 0 |
| 004 | LemmaB | exit 1: `have`-binders blocked `simp` in `experiment_eval`; `transcript_round` simp residue; `Bool.true_eq_false` misuse; `set` left raw form in `hdec` |
| 005 | LemmaB | exit 1: `let` binders in `hdec` blocked `rw` |
| 006 | LemmaB | exit 0 (unused `Nonempty B` warning, removed) |
| 007 | LemmaB | exit 0 |
| 008 | Theorem | exit 1: Sum.elim reduction in `mean_restrict`; implicit `g` under-determined; `complete_resample` rewrite direction; `complete emptyTable` not unfolded |
| 009 | Theorem | exit 0 (two linter warnings, fixed) |
| 010–013 | all four, clean | exit 0, recorded above |

No attempt was memory- or time-limited; no failing job was rerun unchanged.

## Representation decisions (§6: formaliser's choices)

- **Prefixes.** `Prefix X M C = (statement, rounds : List (M × C))`, challenge-
  ending: `(x,(m_1,c_1),…,(m_i,c_i))`; the empty prefix is `(x,[])`. The §2
  message-ending prefix is a `Prefix` plus the next message; `addr` takes that
  pair. Indices are 0-based: the challenge appended to a prefix with `i`
  completed rounds uses `sampler i`, `k i`, `ε i`; §3's `ε_{i+1}` is `ε i`.
  This is forced by (D2)'s shape `(x,…,m_{i+1},σ_{i+1}(a))` (the doomed
  argument ends in a challenge) and resolves the one-challenge offset between
  §2's "prefix of round i" and §3's.
- **Samplers / fresh answers.** The oracle answers a *block* `Fin K → B` per
  address; round `i`'s sampler is `σ_i : (Fin (k i) → B) → C` applied to the
  first `k_i` entries (`k i ≤ K`). (D2)'s density is over `Fin (k i) → B`
  literally; `mean_restrict` shows it equals the density over the block. The
  block is the "fresh answer tuple" of one first read, as Lemma A's statement
  presupposes (a per-cell union bound cannot charge a tuple-level density).
- **Transcript.** `transcript H x π i` recomputes the challenge-ending prefixes
  from the oracle and the proof's messages (`msg π`), the challenge of round
  `i` being the sampler of `H` at `addr (transcript i) (msg π i)`. In the
  memoised experiment the first read of that address returns exactly `H`'s
  block, whoever reads it.
- **Experiment.** `experiment P V x = bind P (fun π => bind (V x π) (fun b => done (π,b)))`;
  one memoised table, so the verifier's re-reads are cache hits.
- **Q_tot.** `distinctFirstReads v = firstReads ∅ v.1`: the number of trace
  entries whose address is absent from the table at that moment. Re-reads
  (including the verifier's challenge re-reads) count zero.
  `firstReadsBound_of_traces` turns the trace bound into the path-wise bound
  `FirstReadsBound` that the induction consumes.
- **Extractor fails** = `extract x T₁ = none` with `T₁` the table at the first
  read of `addr (x,[]) m_1` (§2: words are the preimages present when the
  address carrying their root is first read).
- **Lemma A route.** Direct induction on `lazyMean` (its `none` branch is the
  uniform fresh-answer law; the `some` branch is a cache hit, charged nothing).
  `lazyMean_eq_independentMean` was not used: its `FreshFrom` premise forbids
  cache hits, which the prover-then-verifier program has. R931's
  `adaptive_success_domination` (stage-structured `run`/`step` with
  per-stage mass laws) does not match an arbitrary adaptive `Program` and was
  not used. `CausalFirstHitUnionBound.indicator` is reused.

## Part D — findings

Everything in §3–§5 was statable and proved as written under the readings
below. No premise was added or weakened. Three places needed a reading
decision; each is recorded with the alternative and what it would cost.

1. **(D2) table quantification — provable as written, but note the burden it
   places on instantiation.** The text quantifies "every doomed prefix of
   round i, every message, and every table T", with the extension's
   doomedness evaluated at `T`. Formalised literally: `doomed P T' →`
   (any `T'`) `density{a : ¬doomed (P.ext m (σ_i a)) T} ≤ ε_i` for every `T`
   (`FS.D2`). (D3) is read the same way ("a doomed complete transcript" =
   round-`r` prefix doomed at some table). With this, Lemma B needs no table-
   stability assumption: the flip chain evaluates each transcript prefix at
   its own first-read table and (D2)'s `∃T'` absorbs the mismatch between the
   round-`i` table and the round-`i+1` table.
   *Consequence for instantiation (not done here):* a `doomed` that extracts
   candidate words from the table on the fly cannot satisfy this (D2): with
   `T' = ∅` every prefix is vacuously doomed, while `T` may hold a live
   witness word. The literal (D2) is satisfiable when doomedness depends on
   the prefix alone (IOP-level prefixes carrying the words, with `decode`
   recovering them from the table at first read — consistent with §7 "this
   theorem is about the IOP-level transcript"). If instead the lead wants
   `doomed` to read words from the table, the smallest change to
   FS_GENERIC.md is: state (D2) and (D3) with one table (`doomed P T → …
   ≤ ε` at the same `T`) **and** add to (INJ) the clause "outside the
   collision event, a transcript prefix's doomedness is the same at its own
   first-read table and at the next round's first-read table" (this is §2's
   "a preimage appearing later is a collision event, inside κ" made explicit;
   Lemma B then uses it once per link of the chain). That clause is not
   derivable from (D1)–(D3), so under the same-table reading Lemma B would
   have needed an unlisted assumption — which is why the literal reading was
   kept.
2. **(INJ) and "decodes to that prefix".** With `addr` a function of the
   prefix (§2) and independent of `H`, "two prefixes with equal addresses are
   equal unless a collision occurred" cannot be stated as an `H`-dependent
   event: if `addr` is not injective an adaptive prover chooses a colliding
   message for every `H`, forcing the event to have mass 1; if it is
   injective the event is empty. So (INJ) is formalised as the content Lemma
   B uses (`FS.Inj`): a collision event `Coll` on the experiment's view with
   `mean ≤ κ(Q_tot)`, and, outside it, for every round `i < r`,
   `decode (addr P_i m_{i+1}) (table at that address's first read) = some (P_i, m_{i+1})`.
   `decode : I → Table → Option (Prefix × M)` is part of the address-map
   interface, as the bad sets are "indexed by address and current table".
   An injective `addr` instantiates it with the inverse (unconditionally);
   a duplex instantiates it by walking the table, with the ordering and
   output-collision events inside `Coll`. "First read exactly once" is
   automatic in the memoised model; "was read at all" is the §2 verifier
   property `ReadsChallenges` (V re-reads every challenge address), stated
   as a separate hypothesis because the theorem cannot otherwise know an
   arbitrary `V` reads them.
3. **Q_tot with verifier re-reads.** No obstacle: in one memoised table the
   verifier's re-reads are `some` cells and `firstReads` counts them 0; the
   hypothesis is `∀ H, distinctFirstReads (eval H exp) ≤ Q_tot`. `Q + q_V`
   satisfies it whenever the prover and verifier make at most `Q`, `q_V`
   distinct reads. `κ` is applied to the same `Q_tot`.

Minor: (D2) is stated for rounds `i < r` only (rounds beyond `r` do not exist
in an `r`-round protocol); (D3) treats the complete transcript as doomed iff
its round-`r` prefix is (the final message is a prover message, so no state
is defined after it).

## Where the formal statement differs from FS_GENERIC.md

Nothing in content. The decisions above are representation choices §6
assigns to the formaliser (prefix representation, address-map interface
including `decode`, Lemma A's induction) plus the literal quantifier readings
of (D2)/(D3) recorded in finding 1 and the §2 verifier property made an
explicit hypothesis (finding 2).
