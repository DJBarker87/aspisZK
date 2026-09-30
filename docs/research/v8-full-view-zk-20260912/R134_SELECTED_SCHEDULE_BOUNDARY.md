# R134: complete typed selected-schedule boundary

Source base: `32ccf9a6db2d2aa30ba3e32bc8850f479b04bd00`.

Two focused R19 leaves compile successfully under the recorded 5G/7G,
zero-swap runner.

`SelectedResearchScheduleProgram` is the error-preserving typed callback
schedule through rho.  It directly uses the existing QM31, circle-pair,
nonzero and q22 programs; preserves sampler, circle, nonzero and q22 failures;
and advances the returned state after every absorb or sampler step.

`SelectedResearchScheduleBound.program_within` constructs an all-branches
`Within` certificate of exactly 1815 raw oracle reads.  Its phase accounting
is 132 ordinary challenge reads, 794 circle-pair reads, 594 gamma/kappa/tau
reads, 66 alpha reads, 16 pre-q22 absorbs, 16 q22 reads, one query-profile
absorb and 198 rho reads.  Early error branches terminate within the same
certificate rather than being conditioned away.

This remains a deterministic program/boundary result.  No extracted theorem
yet identifies the actual Rust callback execution with this program.  The
first remaining source proposition is the exact Rust-to-program execution
bridge through rho, including typed error translation and transcript state.
No source distribution, privacy or soundness result is claimed.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r134_evidence.py
```
