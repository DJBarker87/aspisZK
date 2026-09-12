# Validated public terminal context — 2026-09-12

This checkpoint removes caller-supplied public-transition comparison and
carry premises from the abstract selected transfer terminal.

`SelectedTerminalPublicContext.validateTransition` is a fail-closed Boolean
check over independently supplied public and live-account inputs. On success,
the checked theorem constructs the exact `Public` projection used by the
selected semantic rows, the existing `SourceComparisons`, and the digest
selector bits and bounded carry from the same live `nextPairIndex`.

`SelectedTerminalValidatedAfterstate.afterstate_checks_from_validated_transition`
then combines that validation with `RowsVanish` for the same projected table
to construct the complete existing `AfterstateChecks`. Its root-binding
corollary is therefore derived rather than supplied separately.

This is a deterministic abstract/source boundary. Literal Rust parsing and
account authority are intentionally left to the external implementation
refinement premise. The Rust `trailing_ones().min(20)` and bit-shift operations
also still require refinement to the mathematical carry scan and `Nat.testBit`.

The remaining mathematical terminal premise is substantive: the repaired
semantic proof must establish `RowsVanish` for the actual same-body recovered
table. Neither public validation nor this bridge assumes terminal acceptance.

## Focused evidence

Both leaves were compiled on the NUC with Lean 4.32.0, `-j1 -M8192`, and a
systemd scope with `MemoryHigh=8G`, `MemoryMax=9G`, and
`MemorySwapMax=0`. The import path reused pinned, source-identical V7
artifacts; this is not a clean first-party closure rebuild.

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `SelectedTerminalPublicContext.lean` | 0 | 2.87 s | 6,743,220 KiB | 0 | standard only |
| `SelectedTerminalValidatedAfterstate.lean` | 0 | 2.87 s | 6,725,780 KiB | 0 | standard only |

“Standard only” is `propext`, `Classical.choice`, and `Quot.sound`; the carry
projection itself reports only `propext`.
