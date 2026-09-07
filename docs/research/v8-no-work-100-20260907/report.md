# Decision: no investigated candidate is green on all requirements

Recommend **QM31 component-wise two-point OOD tuple binding**, with q21 canonical
fixed fields as the hard-40,000-byte control and q22 as the stronger-margin control.
Fallback: **selective p^8 PCS lifting**, using the new 16×/q16/cap272 model only
after its exact decoder, descent and full-view masking obligations are resolved.
Full quintic replacement is a useful simpler field-size control but currently
misses bytes and gives no evidence for unchanged CU.

These are research priorities, not protocol selections or security claims.
There is no complete V8 theorem, simulator or full-transaction CU result in this
run. A narrower result is established: exact byte/frontier arithmetic, two valid
extension-field constructions, host arithmetic/search costs, and several precise
rejection boundaries. Production files and defaults were not changed.

## First-pass screen

| Direction | Finding and disposition |
|---|---|
| More queries alone | Rejected as a complete fix: gamma 75.74 bits, fold 80.90, conditioned q16 73.01. q21 improves the query component but leaves gamma/fold unchanged |
| Sharper existing mathematics | Already-incorporated weighted-Hensel/Appendix-A.2 work gives about two bits using recorded smaller outer budgets; insufficient alone. New decoding papers do not currently provide an instantiated finite Aspis bound |
| Domain/rate/multiplicity | Exact 36-point parameter screen accompanies the serious rows. m=12 changes the extractor/analysis, not an honest proof-of-work obligation. New circle/GRS/list and curve-cap proofs are required; larger domains alone can worsen polynomial-in-list curve losses |
| Fold/final size | Smaller final messages could save 16 or 32 bytes per value, but require an extra authenticated fold or changed dimension/link. A one-fold final128 cannot be obtained by deleting half of final256. Arity two from dimension1024 gives final512; arity eight gives final128 but doubles fibre values relative to arity four and changes all domain/curve/query obligations |
| Independent batch coefficients | For a fixed unequal vector a fresh full vector dot product has 1/|F| error rather than degree/|F|. This does not fix a post-challenge selected tuple. It also costs extra squeezes and potentially witness/authentication links; fixed-tuple OOD binding is the more developed route |
| Repeat cheap weak stage | Independent fixed-object repetitions can multiply errors. Current gamma/fold failures share adaptive candidate families, so no squaring of the old bound is justified without a joint theorem. Sending another unlinked response is ineffective |
| Full quintic | Both field certification methods pass; same-cap algebraic errors improve by 31 bits conditionally. q21 canonical body 41692, packed 41292. No QM31 embedding; rewrite/port rather than selective substitution |
| Selective octic | Field is certified and contains QM31. Can preserve semantic kernels, but wide challenge dependencies, D masks, malicious subfield leaves, list bounds and full-view simulation remain open |
| New hiding/WHIR/VEIL | Genuine native alternatives with new commitments, masks and openings. None supplies a drop-in authenticated heterogeneous link or a small-instance CU/byte result. No mask-column subtraction credited |
| Lossless compression/six masks | Prior closed experiments reused, not rerun. Generic compression enlarged 30504 to >=30508; degree-ten six-mask transplant is invalid for selected degree27 |
| Checked hints/canonical encoding | Exact inverse equation preserves acceptance and rejects zero/corrupt hints. Host checking is cheaper than inversion, but extra framing/bytes/canonical parsing and actual source integration remain. Prior canonical fixed encoding already spent 320 bytes to save CU |
| Runtime facilities | SHA-512 implemented and observed active on devnet/testnet, absent on mainnet snapshot; no demonstrated Aspis metered saving. Wider digest cannot repair algebraic security |

## Quantitative frontier

All security numbers below are **fixed-bad-object query components**, not full
100-bit certificates. Bytes are exact for the specified model; missing protocol
obligations remain explicit in ledgers-and-candidates.md and candidates.json.

| Model | Body B | vs 40,000 | Uniform / conditioned query bits | Dense arrays MiB |
|---|---:|---:|---:|---:|
| Selected V7 q16/cap203 | 30824 | -9176 | 76.460 / 73.007 | 152 |
| QM31 two-component OOD q21, canonical | 39037 | -963 | 100.361 / same | 152 |
| Same q22, canonical | 40282 | +282; 40-KiB only | 105.142 / same | 152 |
| Same q22, packed fixed (prior branch) | 39934 | -66 | 105.142 / same | 152 |
| Mixed 4× q18/cap265, original no-nonce formula | 40958 | +958; 40-KiB only | 106.954 / 104.671 | 672 |
| Mixed 8× q17/cap278, original no-nonce formula | 40951 | +951; 40-KiB only | 109.508 / 109.287 | 1344 |
| Mixed 16× q16/all schedules, original formula | 40788 | +788; 40-KiB only | 111.063 / same | 2688 |
| Mixed 4× q18/cap246, 24 nonces included | 39994 | -6 | 106.954 / 95.695 | 672 |
| Mixed 8× q17/cap259, 24 nonces included | 39987 | -13 | 109.508 / 103.193 | 1344 |
| Mixed 16× q16/cap272, 24 nonces included | 39980 | -20 | 111.063 / 109.390 | 2688 |
| Full quintic q21, canonical | 41692 | +1692; over 40 KiB by 732 | 100.361 / same | 164 |
| Full quintic q23, canonical | 44276 | +4276 | 109.923 / same | 164 |

The original two tiny 40-KiB margins disappear if 24 nonces are retained:
40958+24=40982 and 40951+24=40975. The original 16× row becomes 40812.
Deleting all three nonce stages is a different transcript and needs its own
compiler analysis; the no-work diagnostic alone does not delete transmitted bytes.

The new hard-cap rows have ideal scan-64 success probabilities about 2.578%,
55.474%, and 99.99999999655%. Their expected attempted candidates are 63.184,
44.158, and 3.188. Thus the 4×/40k route fails the query screen; the 8× route
has severe completeness loss unless the scan is extended. Any extended scan
must be priced at the verifier and counted in the NI resources. The 16× route
has an economical fixed-prefix sampler but only 20 bytes of remaining wire.

The q21 two-OOD historical conditional total is about 100.318 bits, below the
110-bit screening preference but not discarded on that heuristic. q22 improves
the historical conditional total to 104.267 bits. Neither survives as a claim
until restored tuple binding, chord/encoder applicability, masking and actual
NI resource-event bounds are established. Switching to packed fields just to
get q22 below 40,000 risks undoing the measured selected-CU benefit.

## Operation counts and actual host measurements

Minimal binary subtree authentication has q+frontier-1 internal hashes per
tree. The selected maximum has 436 parent and 32 leaf hashes; q21 direct has
608 parents and 42 leaves; q22 has 634 and 44; mixed q16/cap272 has 574 and 32.
These are exact hash counts, not CU. Packed C1 leaf input is 437 bytes and
selected C2 is 220 bytes including tags/salt, requiring seven/four padded
SHA-256 blocks. Mixed C2 is 282 bytes, requiring five blocks. Increased parent
authentication alone must be offset by a real saving to avoid CU regression.

Canonical M31 limb checks rise from 4996 selected to 5980 for two-OOD q21 and
6132 for q22. Mixed q16 checks 6396 limbs. Query recombination still checks all
26+3 columns at four points; p^8 arithmetic is not free just because semantic
arithmetic remains QM31. Final disclosure doubles from 4096 to 8192 bytes in
the selective model. Semantic terminal and pool settlement are intended to
remain the same; no measurement subtracts their cost.

Executed optimized standalone Rust on Apple M3, Mac15,13, 24 GiB RAM,
Darwin arm64, rustc 1.93.0. The final field run: 0.46 s wall, peak RSS
1,671,168 bytes, zero swaps, exit 0. It includes Rabin/Euler certificates,
1000 arithmetic cases, parsing rejection, inverse-hint checks and the narrow-mask
counterexample. Independent Python polynomial arithmetic also passed. A separate
optimized wrapper passed all 32 production field tests (0.37 s wall,
3,063,808-byte RSS, zero swaps), without rebuilding workspace dependencies.
Representative final-run batch means: QM31 multiply 17.6 ns; reference quintic
29.9 ns; octic 37.5 ns; octic×QM31 18.3 ns. QM31 inverse 205 ns versus a
checked inverse hint 15.5 ns, excluding parsing. Logs retain 21-batch means and
p50/p95, sampling/parser results and system resource counters. Timing varied
between runs; these are microbenchmarks, not local proving or CU measurements.

The research SHA-256 scan benchmark ran 2000 public synthetic seeds per hard-cap
row, using macOS CommonCrypto and V7-shaped duplex sampling. Mean/p95/p99 scan
latency: 4× 148/186/302 microseconds; 8× 93/144/149 microseconds; 16×
5.37/14.67/21.25 microseconds. Observed exhaustion counts were 1933/924/0;
exact probabilities come from combinatorics, not those counts. Entire run:
0.83 s, 2,015,232-byte RSS, zero swaps, exit 0. This prototype does not replay
a complete proof transcript or price the verifier's SBF scan.

No honest 2–5-second search budget bounds a malicious prover. The tested compact
search is much shorter on this host; spending seconds on more arbitrary seeds
would require charging their selection power. Checked inverse witnesses and
canonical reconstructions can buy actual verifier arithmetic savings without
soundness credit: verify the exact defining equation, canonicality and input
binding. Two QM31 inverse hints would cost 32 bytes, already too much for the
20-byte mixed-field margin unless offset elsewhere. No such optimization has
yet shown unchanged CU across the four complete transactions.

## Local proving and memory

The 152-MiB QM31 model has the best existing practicality evidence. The prior
V8 branch recorded a V7 fixture run at about 584.5 MB process RSS and 13.61 s
fixture generation (47.01 s entire test command), not a complete V8 prover.
Its q22 rank tests consumed 1.47–1.61 GB for roughly 14–15 minutes. Those tests
were reused, not rerun, and rank-probe memory is not prover memory.

The mixed 16× model's dense arrays alone occupy 2688 MiB. Two full binary trees
over N/4 leaves add approximately 416 MiB in 26-byte digests; per-fibre salts add
128 MiB if materialized. That is already about 3232 MiB before FFT scratch,
masks, quotient arrays and allocator overhead. It cannot claim sub-gigabyte
peak RAM with the straightforward prover.

Out-of-core column/row transposes or recomputation can avoid retaining all dense
arrays. They preserve evidence if the same committed leaves and salts are
reconstructed exactly, but C2 depends on challenges after C1 and queries arrive
after both roots, so a single discard-everything pass is insufficient. A disk
strategy touches at least the 2.8-GB dense object per write/read pass, plus trees;
multiple FFT/transposition passes increase traffic. Leaf-by-leaf naive polynomial
reevaluation would replace FFT work by enormous repeated degree-1024 work.
No sub-multi-gigabyte mixed-field prover or latency was measured; streaming is
a concrete engineering experiment, not a promised 2–5-second fix.

## Stop conditions and next decision

The single most useful next experiment is a **focused exact circle-encoder
bridge/counterexample for the existing two-point chord quotient**, followed by
the restored pre-gamma tuple-family construction if it survives. Use the actual
initial released basis and final fold ordering; test deterministic basis vectors
before any dense rank or SBF work. This precedes an honest V8 prover. Stop the
no-new-tree route if the quotient leaves the asserted code image/degree bound,
or a legal cached/advance continuation violates fixed-tuple selection. Do not
keep the 28-root bound as an assumption to force a green score.

For the mixed-field fallback, first run an optimized small exact full-view
legal-difference rank falsifier including wide D and final disclosure. Stop the
39980-byte profile if necessary masks/link messages exceed 20 bytes without an
identified equivalent saving; also reject the m=12 bound if its exact circle/list
conditions fail. A changed rate/list bound must be recomputed, not grandfathered.

Only after these Gate-1/2 obligations pass is the right next runtime gate a
research-only SBF verifier and all four matched complete transactions, with
expensive accepted schedules, malformed canonical fields, inverse-hint corruption,
sampler exhaustion and unchanged-account rejection. The host has cargo-build-sbf
and Lean launchers, but the pinned release workflow requires Linux x86_64 with
finite no-swap cgroups and cached dependencies. No authorized remote build was
available in this run; no heavy rebuild, remote job or deployment was launched.

The smallest justified **byte-only** relaxation for canonical q22 is +282 bytes;
it fits 40 KiB. Full canonical quintic q21 needs +1692. No justified numerical
CU relaxation is known without full measurements. Missing mathematical and privacy
steps are not a reason to invent one. Failure of these investigated families is
not a general impossibility result.

## Continuation: accepted 40,282-byte allowance

See [chord-verdict.md](chord-verdict.md) for the subsequent exact experiment and
updated decision. Honest chord division fits the released space and final256;
2048 basis cases and 32 fold checks passed. Reverse image membership, transformed
relations and coherent-extraction existence remain unresolved. Canonical q22 is
now the primary size-acceptable model, **not** a demonstrated 100-bit protocol.
The original thresholds below are retained as historical categories.

Further progress: [relation-link.md](relation-link.md) constructs both membership
constraints using only the last three tensor coefficients, and verifies the
relation transpose on all basis vectors. This removes an algebraic ambiguity,
not the adaptive extraction or CU gate. No extra bytes are necessary for these
known-zero linear claims alone; the complete protocol is still unimplemented.

## Answers to the seven decision questions

1. Strongest implementation-backed prospect: QM31 two-point tuple binding; strongest
   simple algebraic field-size control: full quintic. Neither is certified.
2. Best evidence for preserving the selected CU architecture: QM31 route with
   canonical fields and checked computations. No V8 route has measured CU parity.
3. Body models fitting 40000 include canonical q21 (39037), packed q22 (39934),
   and conditional mixed 16×/cap272 (39980). Canonical q22 and the original
   mixed rows only fit 40960, with the nonce caveat above. None is a green protocol.
4. Modest-domain QM31 proving plausibly avoids multi-gigabyte peaks; prior V7
   measurements support that. Dense 16× mixed proving does not; streaming costs
   extra disk traffic/recomputation and remains unmeasured.
5. Checked hints can exchange honest computation/bytes for verifier arithmetic
   without earning security bits. Search can reduce frontiers only with enforced
   selection and its loss/resources charged; no full-CU saving is established.
6. Executed exact combinatorics, independent field certificates, optimized host
   field/parser/sampler/hint tests, and SHA schedule scans. Reused prior Lean/rank/CU
   evidence. No new Lean proof, full-view ZK proof, V8 prover or SBF measurement.
7. Decide the exact two-point chord-to-circle-encoder/fold bridge first.
