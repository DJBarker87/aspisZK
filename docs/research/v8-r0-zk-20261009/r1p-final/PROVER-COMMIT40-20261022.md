# Prover commitment continuation 40

**Target not yet established.** The deployed statement image is D146; the
mask nonce is public and adversary-chosen, including after earlier oracle
queries. D143 observables are public statement bytes, submitted proof bytes
and answers to the adversary's own oracle queries. Timing and other side
channels are outside the privacy contract. Trust list: P1, P7, TrustedStd,
E1 (successful OS draws uniform and independent), E2 (atomic durable ledger).
No OS/fs failure probability or ledger-size restriction is introduced.
The new conditional arithmetic envelope visibly adds `4*Q*attempts/2^256`
(two raw seeds, two worlds) and retains `16*(3/2^256)` for zero exhaustion.
It is proved <2^-100, but is not yet a deployed privacy theorem.

## Stage 1: private raw-seed memo counting

`ProverCommitPrivateMemo40` counts private raw seed suffixes for arbitrary
public prefixes. Both raw derivation inputs for field entropy and all raw
leaf-seed derivation inputs end in exactly their private 32-byte seed.
A query nominates at most one seed. `context_mass` permits arbitrary earlier
context, including adversary nonce selection after queries, followed by the
fresh E1 coordinate. `attempts_mass` combines individually established laws
without independence among events. These are counting lemmas, not a proof
that the complete adaptive runtime satisfies the required laws.

Each raw seed contributes Q*attempts/2^256. At Q≤2^64 and attempts≤128
(16 candidates times eight proof attempts), this is ≤2^-185. Two raw seeds
and two worlds give the explicit addition `4 * budget q attempts`.
No conditioning on nonzero selection is used. No reservation query is charged.

J9172 was a rejected parsing draft (`prefix` is reserved); J9173 compiles the
nine final theorems, exit 0, wall 2.26 s, peak RSS 4,076,840 KiB, zero swaps.
Every printed axiom is in [propext, Classical.choice, Quot.sound]. Full source,
dependency fingerprints and receipts are under
`evidence/prover-commit40-20261022/lean/`. Source revision is the base revision
plus retained exact overlays, not an attribution to a different checkout.

## Numerical before/after

Before (the active endpoint's arithmetic lemma):

```lean
theorem total_lt_target {q r : Nat} (hq : q ≤ 2^65) (hr : r ≤ 2^64) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * ProverCommitSeedEvent19.budget r +
      2 * charge < 1 / (2 : ℚ)^100
```

After (final conditional numerical envelope, not yet installed at the endpoint):

```lean
theorem total_lt_target {scan q attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge +
      4 * ProverCommitPrivateMemo40.budget q attempts + 16 * zeroBudget <
        1 / (2 : ℚ)^100
```

The existing seedGuess charge is retained separately. `zeroBudget` is exactly
`3 / (2 : ℚ)^256`, retained conservatively for the two-slice API; eight
attempts in each of two worlds yield `16 * zeroBudget`. `raw_pair_zero`
proves the two-slice raw-zero bound; `eight_zero` proves the attempt union
without independence between attempt events. Transport to the actual
execution remains an obligation, just as for the memo term. The prior part-39
conditional nonce memo term is superseded for this route by exact public-query
preservation; no uniform-nonce assumption is retained. Native execution and
FS experiment conversion remain to be connected before a deployed headline
can use this arithmetic.

## Stage 2: public nonce and private reservation-history prefix

`ProverCommitPublicNonce40` models the selected API, not `generate()`:
`Raw := Fin 2 → OracleAnswer`, with the supplied public nonce separate from
both seeds. Zero nonce returns RepeatedZeroBlock without an RNG call;
otherwise the recursive owner consumes at most 16 candidates. RNG errors
stop immediately; successful candidates require both private blocks nonzero.
E1 is explicitly specialised to the successful **64-byte** return carrier.
This is the existing named E1 trust item, not an assumption about the public
nonce. No distribution on the nonce is supplied or required.

The prefix retains the ledger36 state/history and reserve implementation.
`reservation_uses_public_nonce` identifies the exact address passed after
successful seed generation. `duplicate_stops` retains the source's abort on
a reused public nonce. `fail_closed` equates the complete failed prefix for
arbitrary real and ideal continuations; `public_reservation` uses the actual
part-39 transition theorem. `adaptive_prefix` quantifies an arbitrary nonce
policy on shared prior context, including earlier adversary queries/answers.
It establishes equality *given* shared context, tape, ledger and schedule;
it does not assume or prove that successful witness-dependent continuations
produce shared context. No ledger cardinality premise or collision term occurs.
`public_reads_preserved` and `memo_preserved` retain ordered public reads,
including repetitions and pre-existing answers.

These are an owned mathematical prefix and read-only source audit, **not**
a new Charon/Aeneas extraction or a native source owner certificate. The
Rust callback is still arbitrary in its type; the experiment must instantiate
it by the selected 64-byte API and the public policy. No claim is made for
callbacks manufacturing deterministic private seeds.

J9174–J9175 were rejected drafts (reserved identifier and alias constructor
qualification); J9176 compiles all eleven theorems: exit 0, wall 2.25 s,
peak RSS 4,162,964 KiB, zero swaps; standard axioms only.

## Exhaustive hash-family classification

`hash-input-inventory.json` pins source bytes, line ranges and excerpts for
every reachable hash family under S2 / private-leaf-salts / r1p-check.
This is a source audit, not a machine-certified whole-program call graph.
Fixtures, legacy profile APIs, test hooks and the unselected unsalted branch
are explicitly outside this call path.

| Inputs | Classification and treatment |
| --- | --- |
| H(public_bytes) | Public-only; preserve existing ROM answer exactly. |
| Reservation domain + public nonce | Public-only; preserve answer exactly and use shared private ledger; no charge. |
| Precommit binding domain + public bytes + tag + context | Public-only, including nonce and statement digest; preserve exactly, no charge. |
| Pool attempt-binding domain + precommit binding + context + fixed descriptor | Public-only despite PRIVATE in the function/domain name; preserve exactly, no charge. |
| Mask-seed and source-seed domains + binding + context + field entropy32 | Raw private field suffix. Two domains, one seed-guess event. |
| Leaf-salt domain + public attempt binding + nonce + tree + index + leaf seed32 | Raw private leaf suffix. All trees/indices, one seed-guess event. |
| Mask expander domain + derived mask seed32 + counter64 | Private-derived; existing protocol-ROM obligation, not public-only. |
| D-seed domain + public attempt binding + derived source seed32 | Private-derived; existing protocol-ROM obligation. |
| Profile21 source expander domain + derived D seed32 + counter64 | Private-derived; existing protocol-ROM obligation. |
| Salted leaf domain/tree + masked semantic values + derived salt32 | Private-derived and semantic; existing commitment/privacy obligation. |
| Binary node tag + child digests, including roots | Private-derived; existing commitment/privacy obligation. |
| Semantic transcript initial/absorb/draw/update and tail transcript/query blocks | Depend on commitments and semantic messages; existing transcript/privacy obligation. |

Absence of literal raw OS bytes does **not** make derived private inputs
public-only. Their old privacy bounds must be transported, not replaced by
the raw-seed counting calculation. Neither the D-seed nor a Merkle hash is
silently assigned an E1 raw-seed law.

`ProverCommitHashClass40.classify` exhausts every constructor of the actual
`LayoutR1PBin.gram` commitment-address carrier. `public_preserved` proves both
public binding branches equal for arbitrary private seed values and leaf
values when their public binding answers agree. `field_suffix` and
`leaf_suffix` instantiate the memo suffix theorem on the actual grammar,
for both field derivation domains and all three trees/indices, symbolically.
J9182 compiles these three theorems: exit 0, wall 2.28 s, peak RSS
4,169,016 KiB, zero swaps; standard axioms only. Rejected name-resolution and
simplification drafts are retained. J9179 was refused as unchanged source
plus dependency fingerprint (a namespace edit failed to match); **no compiler
ran**. The refused pair was not bypassed: subsequent attempts changed source.

## Demonstrated obstruction: the old all-position freshness interface

The next interface is **a public-prefix-aware ROM coupling for the concrete
commitment grammar**, before the native-publication/FS experiment join.
The existing `EventsR1PBin.hit_cm` (EventsR1P4Bin.lean:105–132) obtains
`HitFresh ... (2^255)` for every commitment position. At `qBind 0`,
`LayoutR1PBin.src` chooses secret slot 0, and `hit_cm` varies it with
`secL`. In `GamesR1PBin.SecP`, slot 0 is a hidden uniformly sampled nonzero
nonce. That variation is invalid on the selected D152 carrier, where slot 0
is the public nonce and only the other two slots are private random seeds.

This is a concrete false interface, not an unexplained compile timeout:
`ProverCommitPublicBinding40.grammar_binding` identifies the actual first
binding address for the public nonce. An adversary can query the public
statement digest and that binding before private seed generation. For every
fixed digest and nonce, `public_hit_mass` gives mass **1** for querying that
address on the remaining private-seed carrier. The adversary needs only two
public oracle queries, far within the existing Q budget. E1, E2, ledger size,
source errors and secret-seed guesses play no role in this hit.

`no_hidden_nonce_freshness` proves the old HitFresh conclusion false on this
carrier, using the library's own `hitFresh_mass` inequality.
`public_hit_exceeds_private_charge` proves that charging even the new maximal
four-raw-seed/world envelope cannot cover this certain **public** hit.
J9177 compiles all four theorems: exit 0, wall 1.84 s, peak RSS
4,162,984 KiB, zero swaps; standard axioms only.

This is **not a privacy attack** and does not refute the existing conditional
endpoint. D152's exact public-query preservation is the right repair. But
prefix equality alone cannot instantiate a theorem which requires this
public binding input to be fresh. The required next deliverable must replace
that use of `hit_cm` by a conditional memo-preserving public-prefix law:
start from the adversary's prior public queries and answers, compute/reuse
both binding answers in that same ROM, reserve the chosen nonce in the shared
ledger, and expose fresh private derivation coordinates only off the two
raw-seed memo events. It must transport the resulting **joint adaptive** ROM
law, including duplicate-nonce termination and retained rejected-attempt
history, to the successful source continuation. The private-derived reads
and observer history must retain their existing bounds. No new trust item,
nonce distribution or ledger cap may be substituted for this theorem.

Accordingly, the nonce/reservation prefix is modelled and locally proved,
but the full source owner and the successful-continuation coupling are open.
The native simulator publication, source-to-FSExperiments conversion,
`shippedProverExperiment`, both concrete WholeRunJoins and endpoint without
`RustProverRefinement` are **not established**. They are not replaced with
callbacks or structures that assume their desired conclusions. Per the job's
obstruction-stop instruction, no full manifest, Aeneas replay, Rust build or
shipped-source modification is launched past this false freshness interface.

## Verbatim active endpoint before/after: unchanged

The full module binders and theorem body are retained in identical
`endpoint/before.lean.txt` and `endpoint/after.lean.txt` snapshots.
The active `x : Statement K CommitHandle`, arbitrary `rust : FSExperiments ...`
and `RustProverRefinement` premise remain unchanged. The requested D146
statement-domain, public nonce, environment and memo changes have not been
silently installed into an endpoint lacking the required coupling.

Before:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Retained zero allowance and final verification

The final numerical envelope additionally keeps the zero-candidate term
explicit. J9185 compiles `ProverCommitEntropyCharge40.raw_pair_zero`,
`eight_zero` and `total_lt_target`: exit 0, wall 2.21 s, peak RSS
4,174,204 KiB, zero swaps, standard axioms only. J9184 was a rejected tactic
draft, replaced by an exact rational inequality. The bound is conservative:
the selected API draws two private blocks; the retained per-attempt allowance
is 3/2^256. OS/fs faults and public nonce duplicates remain exactly coupled,
with no probabilistic availability assumption. No zero-failure event is
assumed impossible or silently conditioned away.

J9183 audited the initial 27-theorem cone. Adding the explicit zero allowance
changed that cone; J9186 is the final focused audit of all **30** new top
theorems: target `R1Z.ProverCommitAudit40`, exit 0, wall **1.76 s**, peak RSS
**4,131,900 KiB**, **zero swaps**. Every full `#print axioms` line uses only
[propext, Classical.choice, Quot.sound]. These are focused proof results,
not a release/full-manifest result. Failed elaboration receipts are retained
and never used as accepted theorem evidence.

Task base is `c059caec4afe606fc6f9685851a8989874a8c456`; each attempt records
its exact source SHA256, retained source overlay, dependency-object
fingerprint, command, exit status, wall time, peak RSS, swaps, diagnostics
and full axioms output in `lean/attempts.json` and raw receipts. The final
read-only source/object audit checks the final local module bytes against the
installed host modules and all dependency-object hashes used by J9186.
Only new part-40 modules were installed; no inherited shared source/object
was overwritten. Replaced part-40 drafts were snapshotted by attempt.

All compiler invocations used the pinned Env J launcher on the build host,
Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
Observed reservation was 24 GiB populated plus this 8 GiB scope, below 55 GiB.
No uncapped build, local Lean compile, Rust/Kani, Aeneas, SBF build or unchanged
full regression ran. No full frozen manifest was launched past the failed
public-freshness preflight. Existing runtime/ELF evidence is reused only for
unchanged artifacts, not as proof of the missing source join.

All **491** tracked files under crates/programs match the task base byte for
byte (`shipped-sources-unchanged.json`). No such file changed; the shipped-file
rule therefore does not trigger a three-ELF rebuild. No binary, .olean, ELF,
tarball or local target directory was added. No wallet/account keys or funds
were created, modified or removed. `git diff --check` passes. No push or merge
was performed.

Stage commits: `d2f87886c` (private memo counting), `e92f5e7ac` (public nonce
prefix, hash classification and false old freshness interface); the final
commit contains the retained zero allowance, final audit and receipts.
Next unused assigned Env J attempt: **J9187**. No premise was removed from
the deployed endpoint; the exact next interface is the public-prefix-aware
conditional ROM law described above. The target remains **not yet established**.
