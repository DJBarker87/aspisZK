# Per-block counters

`Port4C_QueryCounters.loop_count` proves the current native loop increments
terms once per actual successful query, preserving its raw length/weight
frames. `Port4C_QueryIntervals.block` starts this count from the SAME native
pending constructor call. `ten_twelve` specializes the two supplied intervals
to terms10 and terms12, with final next22. It does not assert that checkpoint
transport or the independent TX2 Prepared/gamma/proof inputs are joined.

The corrected resumed invariant is terms = next - 10 (when initialized with
next10), rather than terms = next. The existing Port3 terms=next theorem was
explicitly restricted to an initial equality; it was not false. No protocol
or security statement is changed. Allocation/Copy, native push adapter and
other recorded runtime/source boundaries remain. No backend meaning assumed
by this counter proof. Full frozen2 query interpretation is still open.

Accepted010/014, exit0, wall3.382885672/4.782226327s,
RSS4416692/4418092KiB,swap0,standard axioms only. Failed008/012 are excluded
constructor-pattern and numeral elaboration attempts. Exact section6 fields
and axioms lines retained in receipts. Budget14/100 at completion of this
stage (geometry attempts interleaved),0/60 Kani. No shipped changes.
