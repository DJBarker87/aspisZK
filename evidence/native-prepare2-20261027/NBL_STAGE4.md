# Sampler trace replay and caller geometry

NBL_SamplerReplay.low reuses CLOSED LPk_Result.native_result on the SAME full
8-pass trace and derives every digit's canonicality and quotient≤256.
NBL_AddNative.source identifies complete carry/digit carriers from the checked
per-digit trace; canonical derives produced canonicality after each pass.
NBL_DecodeNative.source exports exact raw packed coordinates on that domain.
NBL_SamplerNative composes the installed ordinary and both gamma arms with no
supplied decode output or whole sampler equality. Each gamma increment bound
and subsequent decode/add domain is DERIVED from the same preceding trace.

These are carrier/trace results, not Rust-trace existence assertions. The native
gamma wrapped debug check still requires the second-carry theorem; complete
native routing beyond NBA's terminal second-add cut remains separate.
The inherited native packing gate NBA_K028 is reused, not rerun; the new
coordinate theorem makes its exact pairing explicit. No field multiplication
was attempted in Kani or given a new unpaired arithmetic stub.

Current accepted roots: L017 (carry), L022 (replay), L027 (raw decoder),
L028 (installed full sampler output). Standard axioms only. L020/L021 namespace/
carrier errors and L024-L026 parser/rewrite/import errors are retained, excluded.
L023 was preflight-only missing a redundant direct module import; no Lean ran.
The final decoder instead reuses NBA_ArrayEight.read from the pinned cache,
without copying its proof or adding/rebuilding an unchanged dependency.
Exact source/target/deps/revision/exit/wall/RSS/swap/audit lines are per receipt.

K005 broad y1-error context timed out; K006 split after semantic expansion also
timed out (exit1,104.022020570s,6393408KiB RSS,swap0). Both excluded; no caps or
timeouts increased. Solver cleanup of own NBL_tmp found no matching files.
Further shape review: frozen expand_values ONLY rejects lengths, not contents.
Its reached input464/output928 necessarily pass that guard. Do not keep proving
an impossible injected rejection path. The exact arbitrary-data split/range
geometry is K007: exit0,2.615902986s,334376KiB,swap0;36 checks,1 cover.
Reuse LPt_LPs_ProducerTotal.expansion for total expansion on those lengths;
its native iteration association remains the existing CLOSED leaf evidence.
The full candidate allocation/restoration/native cleanup join is not inferred.

Remaining native members are recorded explicitly rather than promoted to
closure: sampler debug/routing, full query/effects association, candidate
semantic/wide_view failure composition and producer link, whole same-carrier
native prepare trace. Composite stays OPEN, with no headline premise removed.
