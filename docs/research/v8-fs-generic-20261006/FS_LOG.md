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

---

# Addendum 2026-10-06: v2 (rounds as sampler programs) and the duplex instance

Sources: `lean/FS2/{Statement,LemmaA,Theorem,Duplex,DuplexDecode,DuplexDensity,DuplexInj}.lean`.
Same host, toolchain, runner and caps as above (`run.sh`, `-M4500`,
`MemoryMax=7G`); every `#print axioms` is `propext, Classical.choice,
Quot.sound`; no `sorry`/`axiom`/`native_decide`/`admit`/`maxRecDepth`/
`maxHeartbeats` in the sources (grep).

## Why v2

Preparing (INJ) for the duplex of `AspisV8R19.DuplexFrames` showed two
things the v1 statement cannot express:

1. A round's challenge address is `squeeze(bytes(H(absorb …)))`, a function
   of `H`; and `squeeze s'`/`advance s'` are read as a pair in either order.
   v1's `addr : Prefix → M → I` with one block per round fits only a
   one-call-per-round duplex. The tree's sampler laws are stated for sampler
   *programs*, which is the model that fits.
2. A prover may absorb the next message before squeezing the current
   challenge. When round `j`'s chain starts, earlier challenge cells can
   still be unread, so round `j`'s flip depends on cells read *later*. The
   union bound survives by independence (Fubini over the late cells), but
   "decode (prefix, message) at the first read" cannot state it: the
   prefix's challenge values are not yet in the table.

v2 therefore has: `Sampler` (single reads, and `multi` — a nonempty
duplicate-free set of determined cells read in any order); `samp i P m` per
round; `decode a T` returning the *completing sampler* of the round starting
at the first read of `a` (it reads `a`, the round's remaining cells and the
late challenge cells, and outputs prefix, message and challenge); and the
per-read charge `ChainDensity` (the completing sampler's law on fresh
answers), which an instantiation derives from (D2′). `ChainsRead` (every
round reads the oracle) is a structural hypothesis: a read-free round has no
first read to charge. (D1), (D3), `Q_tot`, `maxErr`, prefixes, tables are
v1's.

## What is proved

| Theorem | Content |
|---|---|
| `FS2.chainLemma` | embedded-chain lemma: in any continuation program, Pr[sampler's cells first-read in an admissible order ∧ output bad] ≤ `independentMean` of the sampler; `multi` by permuting means (`multi_erase_mean`) |
| `FS2.lemmaA` | union bound over first reads that decode to a completing sampler, `N·ε` |
| `FS2.lemmaB` | first flip round; (INJ) gives the completing sampler followed to the round's prefix, message, challenge |
| `FS2.theorem4` | `Pr ≤ Q_tot·max_i ε_i + κ(Q_tot)` from D1, ChainDensity, D3, ChainsRead, ReadsChains, Inj, Q_tot |
| `FS2.follow_consistent` | a followed sampler on a consistent trace outputs the oracle run's result (for instantiations) |
| `FS2.Duplex.coll_mass` | collision event (fresh state = iv, = an earlier output, or a 32-byte prefix of an address read so far) has mass ≤ `κ(Q_tot) = 2·Q_tot²/2^256`, by v1's Lemma A |
| `FS2.Duplex.chainDensity` | (D2′) ⇒ ChainDensity for the duplex decoder (`listMean_perm`, `listMean_late_bound`, `samp_mean`) |
| `FS2.Duplex.duplex_fiat_shamir` | the duplex bound from D1, D2′, D3, ReadsChains, Q_tot and `DecodesSpec` |

Duplex model: addresses `Addr L = List.Vector (Option Byte) L` (padded byte
strings of length ≤ L; `toBytes_ofBytes`), frames `absorb`/`squeeze`/
`advance` of `DuplexFrames`, challenge = (value, next state); `samp i P m =
ask (absorb (state P) lbl_i (enc m)) (s' ↦ multi {squeeze s', advance s'}
(acc ↦ (σ_i (acc squeeze), acc advance)))`; `decode` parses the absorb
address (`parseAbsorb_absorbA`), walks the table back through unique
`advance`/`absorb` cells by output (`theUnique`, `walk`), and reads the
missing earlier `squeeze` cells; a fresh absorbed state repeating an earlier
one decodes to a never-counted round-`r` dummy.

## Open: `FS2.Duplex.DecodesSpec`

The deterministic content of (INJ) — outside the collision event, every
transcript round's absorb cell decodes at the table of its first read to a
completing sampler followed to the round's prefix, message and challenge —
is stated as a `Prop` and taken as a hypothesis of `duplex_fiat_shamir`. Its
proof is the table-walk argument: (i) ordering: `advance s'_{i−1}` is read
before `absorb(s_i, m_i)` (else the fresh advance output is a 32-byte prefix
of an already-read address: collision), and `squeeze s'`, `advance s'` are
unread when `absorb` is first read (same reason); (ii) uniqueness: two cells
with equal output are a collision; (iii) `follow` completes because the
verifier reads every chain cell after the absorb's first read
(`follow_consistent`). Estimated several hundred lines of trace bookkeeping;
not attempted in this session.

## Evidence (clean replay, attempts 241–247)

| Target | SHA-256 | exit | wall | peak RSS KiB | swaps |
|---|---|---:|---:|---:|---:|
| `lean/FS2/Statement.lean` | `e472de7d36479495d55e10436635344bf7d2187f223ae73bd0b1db3c78718b36` | 0 | 1.72 s | 3,338,516 | 0 |
| `lean/FS2/LemmaA.lean` | `bc20b02b6cf5b5506acc3887ccd83e571cbcf2934220675fc13bd126275fad03` | 0 | 2.36 s | 3,352,820 | 0 |
| `lean/FS2/Theorem.lean` | `77de94a4a2d61ce458e82d571f7a1f282821816f0be1a8c9fc25c631828abfe1` | 0 | 1.86 s | 3,338,708 | 0 |
| `lean/FS2/Duplex.lean` | `b393d2bea6956eae0635729a5a1c42fe4ef79235654923ee18e844296997359e` | 0 | 2.06 s | 3,352,080 | 0 |
| `lean/FS2/DuplexDecode.lean` | `1d7adcf908b1a9a6236a783b4a6f26b18d575ed083cb34910de023c8ebebf3de` | 0 | 1.70 s | 3,336,860 | 0 |
| `lean/FS2/DuplexDensity.lean` | `f912efd0346c04b20d930b06512c7a792d3e0143dbafc1305914d1c1978eced3` | 0 | 1.72 s | 3,341,660 | 0 |
| `lean/FS2/DuplexInj.lean` | `d1e924dbb826082c0f744cefd031d0f6e3fe27d960e3d5e28b80ed8760e79e5d` | 0 | 1.38 s | 3,323,980 | 0 |

Attempts 200–240: 41 launches, all under the fixed caps, zero swaps, no cap
raised, no unchanged failing job rerun. Recurring causes of failed attempts:
`rw` motives through dependent `Nodup` proofs (`conv_rhs`), higher-order
patterns in `rw` (lemmas restated syntactically), accidental `rfl` closure
followed by dead branches (steps named as `have`s), and — three times — a
defeq or `simp` reaching a concrete `Finset.univ` over `Fin 32 → Byte` or
`List.Vector`, which expands `List.finRange` and hits the recursion limit;
cured each time by stating the counting lemma over an abstract finite type
(the tree's own practice) or by `simp only [protocol]` at reducible
transparency instead of `rfl`. Remaining linter warnings (unused section
variables / simp arguments) are cosmetic and listed in the attempt logs.

---

# Addendum 2026-10-06 (later): `DecodesSpec` proved — the duplex theorem is unconditional

`FS2.Duplex.decodesSpec` and `FS2.Duplex.duplex_fiat_shamir_verifier`
(`lean/FS2/DuplexDecodes.lean`) close the obligation left open above. With
the chain-running verifier `FS2.verifier` (runs every round's sampler program
in order, then decides), the duplex Fiat–Shamir bound

```
Pr_H[V accepts ∧ extractor fails] ≤ Q_tot · max_{i<r} ε_i + 2·Q_tot²/2^256
```

holds from (D1), (D2′), (D3) and the `Q_tot` bound alone; (INJ) is discharged.
All `#print axioms`: `propext, Classical.choice, Quot.sound`; no `sorry`,
`axiom`, `native_decide`, `admit`, `maxRecDepth`, `maxHeartbeats` (grep).

## Proof structure (new files)

| File | Content |
|---|---|
| `FS2/Verifier.lean` | `verifier`/`verifierFrom` (generic), its trace is the concatenation of the chains' traces (`verifier_eval`, `verifier_reads`); `follow_multi_complete`: a `multi` whose cells are all absent from the table and read later on a consistent trace is followed to its continuation on the oracle's values |
| `FS2/DuplexTrace.lean` | trace calculus: `firstIdx`, `Read`, `Before` (total on reads, transitive, irreflexive); `tableBefore_eq`: on a consistent trace `tableBefore ∅ tr a b = if Before b a then some (H b) else none`; `card_dom_lt`: the number of distinct first reads bounds every table's domain; `noColl`, `noColl_injective`, `noColl_prefix_after`: outside the collision event an output is never `iv`, distinct read addresses have distinct outputs, and an address whose 32-byte prefix is a read address's output is read strictly after it |
| `FS2/DuplexWalk.lean` | the transcript's cells `absC i`, `sqC i`, `adC i`, absorbed state `sv' i`, state `sv i`; `chal_eq`, `sv_succ`, `transcript_rounds`, `recs_eq`; `walk_eq`: any sub-table of a non-colliding execution containing the earlier `advance`/`absorb` cells walks back from `sv i` to the records |
| `FS2/DuplexDecodes.lean` | `traceFrom_eq`; ordering: `abs_before_sq`, `abs_before_ad`, `ad_before_abs`, `abs_before_abs`, `ad_before_abs'`, `sv'_ne`; `decodesSpec`; `duplex_fiat_shamir_verifier` |

The argument, as proved: every chain cell is read (by the verifier at the
latest); the fresh absorbed state's bytes prefix the round's `squeeze` and
`advance` cells, so those are read after the absorb; the advance output
prefixes the next absorb, so all earlier cells precede a round's absorb and
are in its first-read table; outputs are injective on read addresses, so the
walk's `advance`/`absorb` preimages are unique and the decoded sampler is the
round's; the absorbed state is not an earlier one (so the collision-guard
branch is not taken); the round's two cells and every missing earlier squeeze
cell are fresh at the absorb's first read and read later, so `follow`
completes; the completion's squeeze values are the oracle's, so the completed
prefix is the transcript's and the challenge is `(σ_i (H sq), H ad)`.

## Evidence (clean replay, attempts 360–370; `-M4500`, `MemoryMax=7G`, zero swaps)

| Target | SHA-256 | wall | peak RSS KiB | warnings (cosmetic) |
|---|---|---:|---:|---:|
| `lean/FS2/Statement.lean` | `e472de7d36479495d55e10436635344bf7d2187f223ae73bd0b1db3c78718b36` | 1.97 s | 3,338,000 | 0 |
| `lean/FS2/LemmaA.lean` | `bc20b02b6cf5b5506acc3887ccd83e571cbcf2934220675fc13bd126275fad03` | 2.69 s | 3,353,044 | 0 |
| `lean/FS2/Theorem.lean` | `77de94a4a2d61ce458e82d571f7a1f282821816f0be1a8c9fc25c631828abfe1` | 2.11 s | 3,338,764 | 3 |
| `lean/FS2/Verifier.lean` | `6ee7184cfb3d8d9a8edc1fcc40f8a80b08d3a48ef6089ee36f40a3a1ae390bf1` | 1.86 s | 3,332,748 | 1 |
| `lean/FS2/Duplex.lean` | `3a2c1330dfd39d59b10cdf1fc68b218432775b855c98e700d1ba938eeac2d88b` | 2.50 s | 3,354,784 | 2 |
| `lean/FS2/DuplexDecode.lean` | `9aa6e9a61007ad3ec6b6dd23cf5cb6edf466306032d9e28de9ce04dddf673f3c` | 2.04 s | 3,337,772 | 2 |
| `lean/FS2/DuplexDensity.lean` | `f912efd0346c04b20d930b06512c7a792d3e0143dbafc1305914d1c1978eced3` | 1.89 s | 3,342,252 | 4 |
| `lean/FS2/DuplexInj.lean` | `d1e924dbb826082c0f744cefd031d0f6e3fe27d960e3d5e28b80ed8760e79e5d` | 1.58 s | 3,325,312 | 0 |
| `lean/FS2/DuplexTrace.lean` | `4bd97d37b38e19e981faa86466182f2ca215b1dcca2c5949f5308710b7d1da9f` | 2.89 s | 3,342,364 | 3 |
| `lean/FS2/DuplexWalk.lean` | `206f5cf79a51b4254d9bf60a70ba85c1b7c188f00e1bbe49445a6319681c875c` | 2.04 s | 3,337,232 | 1 |
| `lean/FS2/DuplexDecodes.lean` | `e0bc8715cb65768fcfaa6dfa1a16fc417693797c0ff0478cc7aba596d169fe93` | 2.93 s | 3,363,136 | 0 |

All exit 0. Attempts 248–356 (109 launches) all under the fixed caps; no cap
raised; no unchanged failing job rerun.

## Engineering note worth keeping

Three times the elaborator hit the recursion limit on terms that were
*syntactically identical* (`h : collOutput T f ⊢ collOutput T f := h`): the
definition's body was a `Finset` membership at `Fin 32 → Byte`, and Lean
unfolded it and evaluated `Finset.univ` (`Fintype.elems`, `Multiset.bind`,
`Fin.foldr.loop`) while comparing `Fintype` instance terms. Cure, applied
throughout: state collision predicates with plain existentials, prove all
counting over abstract finite types, and never let a concrete
`Finset.univ` over `State` or `Addr L` appear in a term that is unified
(`theUnique_preimages`/`theUnique_cellsWith` are stated generically for this
reason).

## Still open (unchanged)

Porting R0's state function to v2 (`R0FS` is on the v1 interface; the v2
challenge is `(value, state)`), the 𝔼 sampler law (`SamplerLaws`), the
`z₀`/`z₁` ledger rows, premise SEM, and the Rust-to-model refinement.
