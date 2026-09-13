# Whole successful source run constructs the live alpha execution

## Result

The promoted theorem is
`FSV8SuccessfulWholeLiveAlpha.successful_whole_constructs_live_alpha`.
Starting only from success of the literal `wholeStagedScript` on one body,
tape and entry oracle, it constructs:

1. the successful source/OOD/gamma prefix and its returned digest;
2. the exact `PreAlpha` value and the fact that the returned prefix digest is
   its stored digest;
3. the successful post-alpha continuation from the actual prefix oracle;
4. the literal `candidateScript` result producing the middle record's
   `alpha0`;
5. live challenge limbs whose exact assembly equals that `alpha0`;
6. the candidate's exact final digest/oracle and the immediately following
   successful query/rho continuation; and
7. the original successful authenticated suffix continuation.

No caller supplies the boundary, candidate limbs, digest equality, live
challenge result, or a coherence certificate.  Abort and error cases are
eliminated by inversion of the one successful whole execution.

This is a deterministic same-body/source theorem.  It makes no freshness,
uniformity, Fiat--Shamir, authentication-collision, extraction or probability
claim.

## New proof leaves

- `FSV8SuccessfulMiddlePreAlphaInversion.lean`: forward inversion of the
  middle bind.
- `FSV8SuccessfulPostAlphaCandidate.lean`: forward inversion of the
  post-alpha candidate bind.
- `FSV8CandidateScriptLiveBridge.lean`: exact candidate-to-live-trace and
  final-state correspondence.
- `FSV8PreAlphaReturnedDigest.lean`: returned digest equals the digest stored
  in the constructed boundary.
- `FSV8SuccessfulMiddleLiveAlpha.lean`: composition for one middle run.
- `FSV8SuccessfulWholeLiveAlpha.lean`: composition from one whole successful
  functional verifier run, retaining the suffix.
- `FSV8ProjectedPrefixProjectionFacts.lean`: an actually returned prefix from
  `emptyOracle` constructs alignment facts against the literal master tape.

All promoted declarations report only `propext`, `Classical.choice`, and
`Quot.sound` under `#print axioms`; no `sorryAx` or custom axiom is present.
A hostile signature review found no vacuous wrapper, conclusion-shaped input,
or stale body/digest/oracle seam.  `LiveAlphaExecution` and
`WholeLiveAlphaExecution` are Prop-valued bundles of concrete run equalities
constructed by the promoted theorems; they are not accepted as inputs.

## Focused evidence

Lean 4.32.0 at commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35` ran on the Tailscale NUC.  Each
leaf used one process under `MemoryHigh=8G`, `MemoryMax=9G`,
`MemorySwapMax=0`, `RuntimeMaxSec=600`, `-j1 -M8192`.  Existing pinned
dependency artifacts were reused; this was not a fresh transitive rebuild.

| Leaf | Exit | Wall | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| `FSV8SuccessfulMiddlePreAlphaInversion.lean` | 0 | 2.67 s | 6,778,156 | 0 |
| `FSV8SuccessfulPostAlphaCandidate.lean` | 0 | 2.84 s | 6,788,380 | 0 |
| `FSV8CandidateScriptLiveBridge.lean` | 0 | 2.66 s | 6,541,500 | 0 |
| `FSV8PreAlphaReturnedDigest.lean` | 0 | 2.77 s | 6,781,288 | 0 |
| `FSV8SuccessfulMiddleLiveAlpha.lean` | 0 | 2.64 s | 6,784,460 | 0 |
| `FSV8SuccessfulWholeLiveAlpha.lean` | 0 | 2.62 s | 6,781,000 | 0 |
| `FSV8ProjectedPrefixProjectionFacts.lean` | 0 | 2.58 s | 6,599,588 | 0 |

Machine-readable evidence, including source hashes and exact command scope,
is in `results/v8-completion-fs-extraction-20260911/whole-success-live-alpha-v1/report.json`.

## Precisely remaining source-to-scheduler boundary

The exact forward scheduler root is already same-body and probability-visible,
but its verifier remains one compiled machine node.  The next theorem must
invert a successful root terminal into the successful functional run above
and construct the internal prefix state on the actual master tape.

The current conservative aligned-alpha consumer asks for 410 calls of room at
the prefix.  That room does **not** follow from success of a realised run: a
successful cache/retry path proves only that its actually consumed calls fit.
The sound next step is therefore a success-local alignment theorem over the
returned scheduler prefix, rather than adding an unexplained 410-call reserve
premise.

The actual-master-tape `ProjectionFacts` producer for a returned prefix is now
proved.  The remaining scheduler work is to obtain the adversary/verifier
returned prefixes from one successful exact-root run and expose the internal
pre-alpha cut without replacing the realised execution by a worst-case room
assumption. Canonical same-body parsing and the typed alpha nonce already have
source producers once the successful record is available.
