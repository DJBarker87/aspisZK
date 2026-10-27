# Recorded workflow deviations

1. The initial trivial Kani probe passed but did not exercise the dependency
   fanout that caused the original compiler failure. Five substantive math
   gates ran before the matched cold dependency probe reproduced that failure.
   The full matched reproduction and fix then completed within three actual
   diagnostic probes, with exact logs in KANI-CONFIG.md. No claim is made that
   the full prerequisite was satisfied before those five early math gates.
2. Following context compaction, Kani gate7 and Lean38391–38393 accidentally
   overlapped. This violated the one-scope instruction. Actual capped receipts
   remain, and all subsequent scopes were sequential. See
   RESUME4-SCOPE-DEVIATION.md. No cap or shared infrastructure was modified.

These deviations do not provide row credit or native verification evidence.
