# Prover commitment continuation 37

**Target not yet established.** Intended trust list: P1 (shared SHA-256 ROM),
P7, TrustedStd, E1 (successful OS RNG draws), E2 (atomic create-if-absent and
persistence). Intended scope: D146 deployed statement image, D143 public
statement/proof bytes and oracle answers; timing and other side channels are
outside the privacy contract. No endpoint premise removal is claimed.

Base: `26b922be6`. Branch: `codex/cx-prover-commit37-20261022`.
No shipped source changed.

## Stage 1: ROM coordinate and event audit

`ProverCommitReservationRom37.entry_mass` proves the entry-count bound for a
fresh uniform SHA-256 ROM answer. `fresh_coordinate` fixes every other ROM
coordinate and permits arbitrary ledger entries depending on that fixed
context. `prior_preserved` proves that the coordinate extension preserves
all earlier distinct queries. These are P1 model facts, without a hash
regularity hypothesis. They do not yet instantiate the source's selected
nonce, nonzero rejection, sixteen-draw generation or eight-attempt owner.

`reservation_length` checks the exact 39-byte reservation domain plus the
32-byte nonce. `not_simulator_seedPoint`, `queried_not_seedGuess` and
`no_existing_event_containment` prove that the existing seed event does not
contain queries on reservation inputs. This is an event-interface finding,
not a claim of a SHA-256 collision or a privacy attack.

J9135 is a rejected simplification draft; J9136 compiles the corrected seven
theorems, exit 0, wall 1.93 s, peak RSS 4,057,200 KiB, zero swaps. All seven
accepted axioms audits contain only subsets of [propext, Classical.choice,
Quot.sound]. Exact sources, dependency hashes and raw receipts are retained
under `evidence/prover-commit37-20261022/`. Each job has its own capped scope
(MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -M7000).
No cold dependency build or full regression ran.

## Stage 2: conditional ROM memo counterexample

`ProverCommitReservationMemo37.generic_memo_mass` computes the exact
conditional ROM mass after one prior query. Fix a nonce `known` and its
oracle answer `entry`; the adversary chooses one ledger entry equal to that
answer. All remaining coordinates stay independently uniform. For an
independent uniform raw nonce the hit mass is `2/N - 1/N²`, N = 2^256,
strictly greater than the fresh-entry bound `1/N`.
`conditional_memo_mass` and `memo_exceeds_fresh_bound` specialize this
symbolically to the actual 256-bit carrier. This is an actual conditioned
ROM model, unlike part 36's generic constant-hash countermodel.
`old_event_absent` proves the old simulator-domain event has mass zero for
that prior query list for every simulator seed. The missing memo-hit charge
therefore matters quantitatively as well as pointwise.

J9137–J9145 are rejected elaboration drafts (decision/Fintype instance
normalization; no resource-cap violation and no recursion limit raised).
J9146 compiles the four final theorems, exit 0, wall 1.97 s, peak RSS
4,061,132 KiB, zero swaps; only standard axioms. This raw-draw computation
is explicitly before nonzero conditioning; no complete native retry bound
is claimed from it.

## Remaining work

The exact native reservation query-event transport is under investigation.
Native simulator publication, source-to-FSExperiments conversion, concrete
experiments, both WholeRunJoins and the endpoint remain open.
