# Runjoin29 — LOG D342 resume

Target not yet established. Stopped at the authorized64 charged Lean attempts:
40 accepted,24 rejected, zero Kani. Exact worktree and branch retained:
`/Users/dominic/ZK/.worktrees/pv-runjoin`, `codex/pv-runjoin-20261026`;
entry `a4e8f7dbad9daeed682b5039e5df7feb507538d0`.

The canonical-route ruling is applied: snapshot decoding precedes the outer
wrapper. The accepted raw-wrapper frontier finding remains valid and is
explicitly excluded from the canonical route. Neither accepted zero-change
finding is retracted, nor is positive change silently declared sufficient.

## Checked results

`CodecSuccess29.iff_path` and `CodecError29.iff_path` characterize, in both
directions and for arbitrary byte slices, the actual EJR-resolved snapshot
decoder's operational success and first-error paths. Header, digest, Try,
field-read and final validation branches are retained. The decoder was split
only by naming unchanged continuations; `DecoderPrefix29.source` proves
equality to the original for all bytes. The staged predicates contain no
whole-decoder call/success premise. Primitive calls remain explicit.

`SnapshotDomain29.source_result` gives the exact semantic guard/error normal
form of the actual extracted snapshot validator. Its success domain is:
nonzero pool/domain; sequence equals index; index below1048576; canonical
current root; all20 frontier digests canonical. `success_iff` proves both
directions. `SnapshotRejections29` proves each rejection with its exact error
and successful-prefix hypotheses: ZeroRequiredBinding,
SequenceIndexMismatch, TreeFull, NonCanonicalDigest.

`DecoderReturn29.validated`, `DecodedFrontier29.decoded_frontier` and
`DecodedDomain29.domain` apply these properties to exactly the actual
returned snapshot, universally over bytes. `DecodedArguments29.frontier`
uses a field-preserving nominal ABI adapter to carry the actual decoder
return into arbitrary compiler arguments. `probe_excluded` proves that the
accepted raw-frontier probe is impossible on this decoded route. This is an
actual decoding association, not an encoding premise or an inferred property
of the raw wrapper.

`CommonDomain29`, `TransferDomain29`, `WithdrawalDomain29` and their `Errors29`
companions prove exact operational success/error characterizations for the
pinned extracted public validators, including first-error precedence.
`PublicDigest29` and `ByteEquality29` identify their native digest and binding
comparisons. `Conservation29` records the variant-specific positivity/sum
conditions and the zero-change/zero-recipient exclusions; bounded summands
cannot overflow u32. These facts do not assert outer-wrapper totality.

`PortDigest29.canonical_iff` proves exact digest-guard semantics in the actual
forest compiler cohort. `PairChecks29.compiler_pair_canonical` proves that
EVERY successful extracted inner compilation, for arbitrary arguments and
primitive dictionaries, has canonical first and second input commitments.
Thus two components of Checked are now derived from compiler success.

`DecodedPackage29.honest_iff` states the exact remaining obligations after
actual decoding and fresh inner-output packaging: Admission AND Checked.
The complete cached payload/both Result layers and canonical frontier then
follow. Packaging is explicitly not substituted for either outer wrapper.

## What remains open

Step1 is incomplete at the OUTER wrapper/inner-call association, runtime and
spent-set checks, membership/value guards, and the remaining primitive totality
and semantic collapse. The public/codec components above are not relabelled
as the complete preparation-domain theorem.

The frozen-source extraction investigation is in EXTRACTION-STATUS.md.
Optimized Charon03 emits both wrapper bodies without translation errors,
with exact source hashes and typed LLBC retained. Some reached ABI types are
still opaque. Aeneas01 refuses the unchanged borrowed-library closure at its
fail-closed loan preflight. The exact escaping-output inventory isolates
core slice Iter::next returning Option<&T>. No iterator stand-in, fabricated
source law, opaque-body success assumption, backend patch or new trust item
is supplied. Complete an owned/P6 immutable-scan association before using
this as an outer source law. This is an extraction obstruction, not a checked
counterexample and not the stop.

Step2 is incomplete: remaining Checked clauses and semantic Admission have
not been derived from every successful outer preparation. Consequently the
requested exact admitted-pair coverage sentence in step3 is not yet justified.
V152–V154 still cover exactly their accepted HonestInput carrier; this run
does not extend that carrier to all canonical-route preparations. Step4,
V038/V045 native execution/observable agreement toward RustRealRefinement,
was not started.

The raw-output probe's proposed inequality failed: raw and field-normalized
owner words give the same commitment and preparation succeeds. Its failed
assertion is retained as a rejected candidate, not promoted to a finding or
used as a stop. No new checked row counterexample is claimed.

## Premises and ledger

Endpoint premises removed/added/weakened:0/0/0. Deployed P OPEN→OPEN.
T remains exactly entropy_law, entropy_kernel, observation. V038/V045/V047
retain their existing scopes. No ROMView, observer, simulator, coupling
marginal or L1/L2/L3 theorem is invented or weakened.

Recount5, quoted: “Deployed PV_Src_Premises remains five fields. No deployed
source-identification closure is inferred.” The inherited honest-family
identification remains accepted. Inherited recount6 totals are407 rows,
OPEN86, CLOSED-ON-CANDIDATE44,400P/3T/4C. No fresh row-count subtraction is made.

Constructed P remains {source public binding, trace}; inherited record counts
2/8/6 are unchanged. No endpoint premise is hidden in a new bundle.

## Validation, receipts and resource discipline

All64 attempts (including the24 rejected candidates) have exact target, exit,
host/SSH wall time, peak RSS, swap, source revision/blob/SHA, dependency
fingerprint and axiom output in receipt-index.tsv and receipt-*.json.
Every final source matches its accepted retained snapshot and git blob.
Failed snapshots and compiler diagnostics, including diagnostic-generated
sorryAx lines, are retained; none is accepted or imported as a proof.

The single final endpoint/domain audit42399 passed: host wall0:01.94,
SSH wall2.2020877092145383s, peak RSS5,010,583,552bytes, swap0,
source revision8686618c26a8e632b2aa6bb430993d1ed0cd740b. All30 printed axiom reports
are subsets of propext,Classical.choice,Quot.sound, including every audited
root, honest-family identification and privacy_headline_deployed. The full
statements of HonestInput, the snapshot domain, residual honesty obligations,
RustRealRefinement and the unchanged endpoint are retained in its raw log.
This is focused validation against the coherent pinned cache, not a new
release build or full frozen-manifest replay.

All scopes were sequential MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64;
Lean-M7000. Overall Lean peak RSS5,010,583,552bytes; all swaps0; no memory cap
raised, no timed-out/memory-killed job rerun, and no unchanged source/direct-
dependency fingerprint repeated. Three aggregate-reservation refusals were
uncharged; fresh IDs and all mandatory180-second intervals are validated in
admission-intervals.json. IDs38183–38193 and42300–42354 are retired, plus final
audit42399. IDs42355–42398 remain unused; the compile budget is nevertheless
exhausted. Prior-run audit IDs38194–38196 were not reused.

The exact decoder source is EJR-resolved, not the similarly named tracked
variant selected by a grep hit. Before the first compile, all5673 external
objects matched h4/SCOPE. The final closure resolves1448 project modules,
no unpinned module and no XR import. All1448 private-cache source checks
match their authorities; h6 verifies669 reused replay roots and785 transitive
fingerprints with matching toolchain/prefix. Only own private source/object
paths were written. Generator --check passes for public success/error paths,
unchanged decoder splitting and staged codec domains. The omitted duplicate
source bundle can be reconstructed from exact blobs in focused-resolution.json;
generators now read that authoritative blob directly.

Native/translation investigations were also capped, sequential and swapped0:
raw-output candidate exit101,wall0.5064784539863467s,peak185782272bytes;
Charon01 exit101,wall40.78086021001218s,peak1318473728bytes;
Charon02 exit0,wall39.8743476519594s,peak1314856960bytes;
Charon03 exit0,wall49.26124391396297s,peak1288577024bytes;
Aeneas01 exit2,wall0.6046677060076036s,peak74485760bytes.
Native source/library/writer/manifest files were byte-checked before these
runs. All Rust commands use --release,-j4 and explicit optimized flags;
expected time was named compilation/translation or the tiny guard probe,
not dense arithmetic. Extractor hashes match inherited pins in a separately
labelled post-run read-only check; this is not a loan/fidelity certificate.
No successful Aeneas emission or outer source theorem is claimed.

No shipped file under crates/ or programs/ changed. No key operation, new T
field, observer/simulator/bad-event change, push or merge occurred. No binary,
olean or ELF is committed. Existing pinned build caches are retained for the
next focused dependent proofs. final-check.py validates the source/git
snapshots, accepted axioms, all receipts/caps, refusal intervals, ID collision
checks, source authorities and unchanged frozen directories.

commits.txt records git log --oneline a4e8f7dbad..HEAD through the proof stages;
the final evidence commit follows that list. Branch is unchanged.

Next concrete deliverable: complete the owned/P6 immutable-scan and exact
outer ABI/compiler-call association; compose all runtime/spent-set/value/
membership guards with the checked codec and inner success/error domains;
derive remaining Checked and Admission; then state exact admitted-pair
coverage. Only after those proofs proceed to V038/V045. Target not established.
