# DualPad focused Lean replay

This is a standalone field-algebra lemma receipt, not a privacy or protocol
theorem. The source snapshot `R1DualPad.lean` has SHA-256
`5e8696117c92eb22cee3536ac3594c6eeaed95773f31d076e87078fcc8030c5e` and was
checked from local worktree revision `7742957648c33cf045eb6a672e7c7cc796b61087`
(branch `codex/100bit-spend-path-20261013`). The same hash is in the NUC `sha-`
receipt for the successful replay.

The focused target was only `R1DualPad`; no package replay was run. Exact
successful invocation on the NUC was:

```sh
cd /home/dombarker/project-offloads/aspis-fs-generic-20261006
./run2.sh dual-pad-r1-20261013g R1DualPad 5000 6
```

The runner used Lean `leanprover/lean4:v4.32.0` and executed the equivalent
focused command with `-j1 -M5000 -DElab.async=false -R <sources> -o
<objects2/R1DualPad.olean> <sources/R1DualPad.lean>`. Its systemd scope used
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`; the reservation check reported
24 GiB populated plus this 6 GiB scope (30 GiB total against the runner's 55 GiB
limit).

Successful attempt `dual-pad-r1-20261013g`: exit 0, wall time 0.79 s, peak RSS
1,637,108 KiB, swap 0. `#print axioms` reported:

```text
AspisR1.DualPad.corrected_first_equation:  [propext, Classical.choice, Quot.sound]
AspisR1.DualPad.corrected_second_equation: [propext, Classical.choice, Quot.sound]
AspisR1.DualPad.determinant_expansion:     [propext, Quot.sound]
```

Earlier attempts are preserved verbatim in `remote-evidence/`: attempt `a`
failed before Lean because the remote source had not yet been copied (exit 1,
0.04 s, 83,780 KiB, swap 0); attempts `b` through `f` exposed proof-script
issues (each exit 1, under 1 s, 1.63 GiB peak RSS, swap 0). The source SHA for
each actual compilation attempt is preserved alongside its output and timing
log. Attempt `g` is the final source snapshot archived here.

An unrelated reservation probe later invoked the same Lean runner with the
module memory threshold incorrectly set to 100 MB. Lean's interpreter aborted
at 1,368,552 KiB after 1.51 s (signal 6; no swap); the output, timing, and
source-hash files are retained as `*-check-auth-gate.*`. This was not a replay
of the DualPad target and produced no accepted result or target artifact.
