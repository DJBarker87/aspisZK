# LineFold focused Lean receipt

This is standalone exact field algebra for the four-value line fold. It proves
the stated coefficient recovery identities and the Horner recombination under
the listed nonzero assumptions. It does not prove domain commutation, a
bad-set bound, or an encoder property, and it is not connected here to the
protocol's natural-basis implementation.

The final source is
`docs/research/100bit-spend-path-20261013/lean/LineFold.lean`, SHA-256
`a74b9e3e7987ba420e138e889efc2757ef10d45d12781c8b8c2b98c12e752981`.
The source worktree revision was
`7742957648c33cf045eb6a672e7c7cc796b61087` (source was uncommitted). It was
compiled in `/home/dombarker/project-offloads/aspis-fs-generic-20261006` on
`nuc`, with Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`; the environment manifest SHA-256
was `ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`.

Successful capped command:

```sh
./run2.sh line-fold-r1-20261013d R1LineFoldD 5000 6
```

`run2.sh` reported a 24 GiB populated finite-cap reservation plus this 6 GiB
scope (30 GiB of the 55 GiB limit). It ran Lean with `-j1 -M5000
-DElab.async=false`; the systemd user scope had `MemoryHigh=4G`,
`MemoryMax=6G`, and `MemorySwapMax=0`. Result: exit 0, wall time 1.16 s,
maximum RSS 1,641,760 KiB, swap 0. The final `#print axioms` output for each
of `recover_h0`, `recover_h2`, `recover_C0`, `recover_C1`, `recover_h1`,
`recover_h3`, and `recovered_horner` was `[propext, Classical.choice,
Quot.sound]`; no `sorryAx` appears in the successful target.

The receipts preserve the three failed focused attempts and the successful
fourth attempt. A failed target's axiom printout can include `sorryAx` after
Lean reports declaration errors; only attempt D is successful.

| Attempt | Source SHA-256 | Exit | Wall | Max RSS | Swap | Outcome |
|---|---|---:|---:|---:|---:|---|
| A | `a233f0b74afb3e847443ba06885e9e5056738bada33676aab8bd1077c707fc05` | 1 | 1.02 s | 1,625,552 KiB | 0 | Horner calls supplied an extra unused coordinate argument. |
| B | `3fef1e0dcba83c015cbda4a453b2cc796669bf11ed71c2a0a9f5804895d295ae` | 1 | 1.29 s | 1,633,780 KiB | 0 | Theorems did not retain nonzero assumptions in their types; C1 cancellation also remained. |
| C | `aac1d9e550eae8d34c7d9e17b39fb517e871cfaa5d381a257341bff784a8cbbc` | 1 | 1.16 s | 1,631,540 KiB | 0 | A no-progress `simp` step left `sorryAx` downstream. |
| D | `a74b9e3e7987ba420e138e889efc2757ef10d45d12781c8b8c2b98c12e752981` | 0 | 1.16 s | 1,641,760 KiB | 0 | All requested identities compile. |

For each attempt, `sha-*`, `out-*`, `time-*`, and the exact source snapshot
are archived beside this README. The source file in `lean/` is the successful
attempt D.
