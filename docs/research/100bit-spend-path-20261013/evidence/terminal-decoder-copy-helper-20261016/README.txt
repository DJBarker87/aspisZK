ASF8 decoder Copy-helper extraction and regressions, 2026-10-16
Production source0626294e34632812accf4cb14704f027368ea871; baseline42e5ca201.

Final source:8 digest limbs and two20-node frontiers are evaluated in ascending
order; seven fixed RHS arrays use their full slices; two reserved-byte checks
use ordered short-circuit ORs. Forty fixed slice conversions use one actual
source-owned unwrap_fixed_slice<T:Copy> helper, with concrete TryFromSliceError.
The helper returns the Ok value or literally panics. Inspected enclosing guards
make its Err branch unreachable. Its panic text differs for arbitrary helper
inputs; no arbitrary-input panic-observational equivalence is claimed.

Two independent reviews checked cumulative offsets, dimensions, guards and
error order against42e5/72a. Current field/QM31 source is untouched.
Charon and the private geometry-fixed Aeneas both succeeded. Four name-only
constructor metadata changes invert to the entire original LLBC JSON. Generated
Types/Funs are preserved unchanged. The geometry tool source/binary/build pins
are in aeneas-decoder-geometry-20261016. No downgrade or generated-body repair.
Actual Lean compilation and declaration axioms are a separate C evidence gate.

Measured jobs (all exit0; times seconds; RSS KiB):
Charon72.176 /672648; Aeneas22.813 /4242104;
native optimized build67.146 /548680; trace0.159 /1936;
saved-proof counter52.079 /541872; SBF40.050 /674472; CU pair0.201 /28972.
Translation/native scopes6/8GiB; Rust regression scopes8/10GiB; all swap0.
Full command, source, runtime and cgroup receipts are retained. No full replay.
The20,720-case trace agrees in all66,622,110 bytes with the retained baseline.
Multi-error corpus cases mainly test magic-error precedence; deeper ordering
was inspected in source, not exhaustively tested or universally proved.

One before/after admitted [3,10]+ASQ8 fixture, excluding setup:
stage1 1342259 ->1343603 (+1344CU);
stage2 1229076 ->1229578 (+502CU); total+1846CU.
Initial accounts, checkpoint and ASR8 outputs agree; both stages accept.
Candidate ELF SHA835ccf148744c242e6bb912fed19971dc5d8e660a6c7abde2d50aa206241f8c6.
Existing point_claims stack diagnostics are retained; no general stack-safety
or universal source QV/compiler-correctness claim. Keys retained0600, excluded.
All unsuccessful predecessors remain committed separately with their failures.
