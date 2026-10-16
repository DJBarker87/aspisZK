# All-round adaptive raw-byte decoder and conditional membership bound

`FullPublicTotalCase` combines all 33 public-recovery cases and reuses canonical-row-zero transport. `RawFullPublicSelection` preserves that recovery on actual unrestricted-byte oracle traces. `RawFullPublicRun` identifies the statement chosen by an actual adaptive prover, without supplying it to the decoder. `RawAdaptiveCompiledCompletion` returns exactly the compiled protocol transcript/message/challenge for every row; commitment words and public statement are recovered from the current address/table.

`RawAdaptiveDecoderInjection.injection` instantiates the acceptance-scoped first-read interface, including the eleven-target collision event and its proved mass `12 Q² / 2²⁵⁶`. Formatting is needed only when the original verifier accepts. `RawAdaptiveMembershipBound.membership_bound` discharges recovery, density, D1 and chain-read obligations and transfers the bound losslessly to the original adaptive prover.

Its remaining source-facing premises are explicit: accepted executions supply the valid constructor schedule, tag 2 and strict row2/30 commitment payload parses; terminal D3 holds outside the shared collision event; and the complete original experiment has at most Q distinct first reads. The conclusion is the symbolic ROM membership-error bound `Q * maxErr(LiteralClassifier.budget,33) + 12 Q² / 2²⁵⁶`, with no union over public statements and no adversarial hash-input-length assumption.

The clarified 100-bit per-attempt bound is a separate fresh-challenge statement. This result does not remove the query factor from repeated/adaptive oracle attempts. Source correspondence, terminal checks, efficient extraction and privacy/runtime closure remain open; the complete spend security claim is not yet proved.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `FullPublicTotalCase` | 1.784 | 3552552 | 2 |
| `RawFullPublicSelection` | 1.787 | 3651064 | 2 |
| `RawFullPublicRun` | 1.821 | 3651676 | 2 |
| `RawAdaptiveCompiledCompletion` | 1.707 | 3651508 | 1 |
| `RawAdaptiveDecoderInjection` | 1.659 | 3642420 | 1 |
| `RawAdaptiveMembershipBound` | 1.612 | 3652452 | 3 |
