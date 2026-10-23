# Actual accepted call-site state threading

Port2_ReturnedState, attempt005: exit0; wall3.3686838599969633s; peak RSS4401204KiB; swap0; source revision and exact hashes/deps in receipt. finish_prefix and writer_returned use standard axioms only. Attempt004 was an excluded reserved-keyword elaboration failure.

TX1 writer and TX2 finisher receive their actual query return and Vec back-write; all prior stage child returns come from that same accepted execution. This closes caller state provenance at those cuts, not any concrete BodyJoin or frozen2 identity. Batch, geometry, pending, query and flush exact remaining gaps are recorded in design/PORTS2-20261023.md. No headline premises removed/added.

Attempt006 launched no Lean: missing Stage2AccumulatorStep object in host path, failed preflight. Its launcher and reservation are retained. The next stage isolates the inherited query definitions in new Port2 modules rather than overwriting a shared object or starting a cold build. At this stage: 5 actual Lean compiles/100; Kani0/60. No timeout, kill or unchanged rerun.
