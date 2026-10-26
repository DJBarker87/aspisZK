# Four-byte induction and reservation retries

JFz_Canonical.nil and JFz_Canonical.cons4 compile on the coherent host workspace.
They use [propext, Quot.sound]. This is a generic helper for bounded word checks;
it supplies no complete scan, wrapper acceptance, or actual-top premise removal.

JFz_001: exit 0, wall 3.0873936699936166 s, peak RSS 4254456 KiB, swaps 0.
The exact command, source revision/hash, imported-object hashes, cgroup limits,
and printed axioms are retained in JFz_001/receipt.json. No shipped files changed.

The first attempted JFz_002 launch was refused before compilation. Aggregate
reservation was 51942260736 bytes; adding this job would reserve 60532195328,
above 55 GiB. Retries 1 and 2 after at least three minutes returned the same
aggregate refusal. These are admission checks, not Lean attempts. No barrier
was bypassed. The generated concrete targets are not yet validated.
