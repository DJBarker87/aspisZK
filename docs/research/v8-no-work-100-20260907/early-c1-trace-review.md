# Actual-answer C1 prefix and the same genuine payment execution

Research source pin `bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee`.
The two instrumentation hooks are host-only under `v8_early_prefix`; no
production or SBF acceptance, transcript bytes, or proof grammar changes.

## What executed

The existing genuine synthetic transfer producer runs its real compiler,
masking, C1/C2 encoders, sequential OOD claims, semantic producer, shifted
ordinary rows, carried image weights, compact relation and shifted query batch.
One seed (1) is predeclared. Query-nonce search and external context override
are disabled. The authoritative synthetic fixture context is reused; this is
not the complete pool program or a live account/registry transaction.

The actual shared SHA gateway records `(concatenated input, returned 256-bit
answer)` in memory, beginning at entry to the producer execution. The C1
prefix is frozen immediately after its tree/root is constructed, **before**
`start` samples lambda and chi. No later C2 choice, OOD response, gamma,
folding challenge or query schedule enters this stored prefix.

The new resolver receives only these answers and the root. It looks up the
first matching 208-bit digest, parses the literal leaf/node preimage, and
follows high-to-low position bits for 18 levels. It neither rehashes inputs
nor computes default subtree digests. Missing or wrongly typed preimages
retain their first-unresolved target; the separate totalized-leaf operation
returns a zero leaf. Noncanonical packed bytes remain raw: field parsing and
its `Option.getD(0)` convention are separate downstream operations.

This matches the shape of `V7MerklePartialPathExtractor.resolvePath` and the
new finite-prefix Lean definitions. It differs intentionally from the older
complete `c1_query_graph.rs` extractor, which rehashes entries/defaults,
requires child-before-parent query order, and reconstructs a whole tree.
Neither is a public-root-only extractor. The new Rust code is **not** a
translated-source proof of equality with the Lean resolver.

A separate recording captures the public verifier call on the produced body.
For each of the 22 actual scheduled positions, the test resolves both the
early prefix and the verifier's recorded path, and compares the raw 403-byte
C1 leaf and 32-byte salt with that proof record. All 22 agree, with 19 recorded
path nodes each. Root identity, slot ordering and salt offset (589) are checked
within the same execution; producer coefficient arrays are not resolver inputs.

## Exact evidence and limits

| Item | Executed result |
|---|---:|
| Early raw hash calls | 1,051,764 |
| Distinct early inputs / projected digests | 789,620 |
| Early raw input bytes retained transiently | 238,287,374 |
| Verifier-call recorded SHA calls | 2,812 |
| Accepted C1 openings checked | 22 |
| Recorded path memberships checked | 418 |
| Resolver oracle/hash calls | 0 |
| Actual body | 39,502 bytes |
| Unchanged maximum body | 40,282 bytes |
| Positive grinding credit / nonce search attempts | 0 / 0 |

The 2,812 count includes the host's existing dense-v2 differential relation
replay. It is **not** the selected SBF call count or a universal verifier
resource bound. No C1 trace, salt array or secret material is written out.
Existing producer output contains only synthetic public proof/context files.

The separate optimized controls cover all 96 combinations of a depth-one
tree's prefix subsets, input permutations and positions; they include missing
nodes, malformed types, preserved noncanonical bytes, fuel/position failures,
full-answer inconsistency and truncated collisions. Those are exact resolver
controls, not exhaustive adversarial strategies or probability experiments.

Apple M3 / Mac15,13, Rust1.93.0, offline locked Cargo release, overflow checks:

| Stage | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| Optimized resolver-test compile | 0 | 0.64 | 149,700,608 | 0 |
| Three control tests | 0 | 0.37 | 2,097,152 | 0 |
| Changed instrumented host build | 0 | 45.39 | 805,617,664 | 0 |
| One genuine instrumented execution | 0 | 7.96 | 664,453,120 | 0 |

The instrumented producer reports 6.2333 seconds excluding its 1.2932-second
setup. These numbers include recording/indexing overhead and a non-final host
optimization configuration. They do not replace the earlier NUC proving or
complete-transaction CU measurements. No SBF build occurred.

Public artifact SHA-256 receipts:

- Proof: `b2ad1b63fca437acd86a2574404a1263c0fc293520cf526c313a5d82987d5ce1`
- Public input: `76f29db662d14513be3925975d57bd49663acd630666e89c9b16e2ec68caf9ea`
- Transition: `f9474caef25594cf4fffd608428c482485f2764c5cc4da3eafdd5231a5e39766`
- Binding: `1f46700845c22fb7e696f2db3f95a0ad06a2694e0deeebe27f35912887a243b7`
- Instrumented executable: `4a67efda9d568dffec0767aa504b4720445f167a3feeb0dfa6515aea0d210471`

Logs: [controls](evidence/early-c1-trace-controls-v1.log),
[payment build/execution](evidence/early-c1-trace-payment-v1.log).

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_trace.sh \
  controls /tmp/aspis-early-c1-controls-new.log
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_trace.sh \
  payment /tmp/aspis-early-c1-payment-new.log
```

Both commands use a process-tree RSS guard at 7 GiB and refuse to overwrite
logs. The expensive phase is optimized host compilation. No unchanged full
suite or SBF build is requested. Additional public fixtures use a fresh
temporary directory; raw oracle records never leave memory.

## The next missing implication

This establishes a concrete honest source-interface control. It does not
prove that **every** adversarial V8 execution induces the bounded lazy-oracle
strategy, that the extractor can rewind it within budget, or that acceptance
enforces the semantic equations. The partial resolver may legitimately return
defaults on malicious prefixes, and later authentication exceptions must be
charged in the shared hash experiment. Neither unresolved paths nor provider
abort/fuel/replay failures disappear from accepted extraction failure.

The new finite lazy-oracle game is the probabilistic counterpart; its modeled
calls must still be coupled to the actual source and declared global resource
budget. Merely observing a SHA implementation's outputs in this fixture does
not prove a random-oracle law for SHA-256.
