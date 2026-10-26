041 did not reach scp/Lean: reservation scanner reported a vanished foreign
cgroup run-r211a38599e8940af80ab27f677504c98.scope. Per local-lean rule7,
wait30seconds and retry reservation once. The existing inherited orchestration
had already waited during contention, so its retry==0 condition did not perform
that permitted vanished-cgroup retry. No launcher/infrastructure is modified.
Original diagnostic is retained in JFs_041-first-barrier-failure.log.
