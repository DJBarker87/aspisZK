# Equality loop, scalar arithmetic and fold-order evidence

Seven selected Lean 4.32 targets, 13 standard-only axiom reports, 31 retained
attempts (23 failed). The generated slice has no axiom reports and is counted
only as a successful compile. No full regression or dependency rebuild was run.

The archive contains exact sources, successful output objects, raw receipts,
logs and resource records. `root-review.json` is an independent review of 302
checksums, 15 archived custom objects, selected raw axiom logs and represented
import edges. It reconciles the previously checked `R0P.SemDecision` source
and object without changing the original import receipts. Three historical
Horner declarations are reused verbatim with fresh module framing; the final
targets do not import the old broad `SourceMixing` object.

To reproduce the evidence audit, unpack `equality-terminal-evidence.tar.gz`
and run `python3 audit-bundle.py PATH/aspis-r1-equality-value-bundle-20261016`.
This checks retained evidence; it does not replay Lean.

The isolated broad-import scratch attempt's memory exception (exit 134) is
retained. It was replaced with the minimal declaration slice, not retried
with a larger cap. Every run used MemoryHigh=4G, MemoryMax=6G, swap=0,
TasksMax=128, Lean -j1 -M5000, and a 300-second timeout.

The actual equality loop is related to the existing mathematical equality
product for canonical inputs. The scalar result covers eight field calls;
the Horner result is pure fold algebra with explicit array-to-lane hypotheses.
The full terminal wrapper, source/model correspondence, security theorem and
runtime release remain open. This evidence does not change production Rust.
