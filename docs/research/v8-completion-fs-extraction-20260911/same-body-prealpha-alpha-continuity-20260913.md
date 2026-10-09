# Same-body pre-alpha to live-alpha continuity

Date: 2026-09-13

Status: checked deterministic source-execution milestone. It assigns no
probability and does not claim global soundness.

## Result

The promoted theorem is
FSV8PreAlphaAlignedChallenge.successful_preAlpha_then_alpha_constructs.
It starts from success of the existing preAlphaScript and success of the live
challenge at that script's exact returned digest and oracle state.

The theorem constructs:

- the hidden boundary immediately after response0 and before the alpha nonce;
- the canonical typed alpha nonce from the same parsed body;
- the literal one-query marker continuation;
- equality of that continuation's complete result/oracle pair with the
  original successful pre-alpha execution;
- equality of the marker transcript with the live challenge's starting
  transcript; and
- the complete aligned one-to-four output/advance alpha challenge execution.

The returned proposition retains the actual live challenge result equality.
It therefore cannot silently replace source success with decoder acceptance
alone.

successful_beforeAlphaMarker_digest follows every inactive, kappa, functional,
tau and response0 branch and proves that a successful prefix's returned digest
is the digest stored in its constructed boundary.
preAlpha_success_constructs_before_marker_full then exports the complete
post-marker oracle equality, rather than only equality of returned values.

## Same-body scope

The alpha nonce is the source slice body[11204..11212], obtained through the
canonical fixed-field parser's successful length/shape guard. No nonce,
boundary, marker state or alternate body is independently supplied to the
promoted construction.

The top theorem still accepts preSuccess and liveSuccess as source-success
facts. They refer to the same body and the latter starts at the exact final
digest/oracle of the former. The next root decomposition must construct both
facts, the initial aligned state, parse success and room bounds from one
successful whole selected-verifier execution.

## Evidence

Focused Lean 4.32.0 builds ran on the NUC over Tailscale under
MemoryHigh=8G, MemoryMax=9G, MemorySwapMax=0, RuntimeMaxSec=600,
-j1 -M8192.

Machine-readable source/artifact hashes and resource measurements are in
results/v8-completion-fs-extraction-20260911/same-body-prealpha-alpha-continuity-v1/report.json.
All five leaves exited zero. The promoted theorem uses only propext,
Classical.choice and Quot.sound; no sorryAx or custom axiom appears.

A hostile signature review found no stale-oracle substitution, independently
supplied hidden boundary or conclusion-shaped coherence input in the revised
chain.

## Remaining boundary

The next theorem must decompose one successful exact whole selected/factored
verifier run to construct:

1. the actual pre-alpha entry states and their V7/finite-transcript alignment;
2. the upstream out, gamma, z and digest;
3. canonical parse success for the same adversary-returned body;
4. preSuccess;
5. the immediately following live alpha success at its exact returned state;
6. total/fresh/tape room from the root limits.

Programmed restoration, allowed-access payment extraction, adaptive
Fiat--Shamir probability transport and literal Rust refinement remain
separate later gates.
