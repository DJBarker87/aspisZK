# S9 compute attribution and narrow candidates

Measured candidates only; none is adopted. The approved comparator is artifact `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`. The allowance remains +12,000 CU per phase. This packet does not establish worst-case cost, source refinement, or 100-bit soundness.

The current owned adapter with frozen C arithmetic exceeds that allowance by 1,982 CU on the six deterministic partial-mask fixtures. Original fast-pairing code saves 872 stage-1 CU; original weights saves no stage-1 CU and worsens settlement. The owned adapter contributes another 2,293 stage-1 CU relative to the historical caller. This isolated the zero scanner and Dot.finish as useful narrow targets.

| Case | Change from frozen C plus current owned adapter | Maximum stage-1 delta vs approved S4 | Maximum settlement delta |
|---|---|---:|---:|
| C | Baseline candidate | 13,982 | 2,294 |
| H1 | Original fast-pairing bodies | 13,110 | 2,294 |
| H2 | Original weights | 13,982 | 11,306 |
| H3 | OR8 zero scanner | 13,762 | 2,294 |
| H4 | Word8 zero scanner | 17,078 | 2,294 |
| H5 | Tail-slice zero scanner | 12,214 | 2,294 |
| H6 | H5 plus inline snapshot | 12,262 | 2,462 |
| H7 | H5 plus checked_q ok_or | 12,214 | 2,294 |
| H8 | H5 plus all original fast-pairing bodies | 11,342 | 2,294 |
| H9 | H5 plus inline zero scanner | 12,214 | 2,294 |
| H10 | H5 plus inline Dot.finish | 12,214 | 2,294 |
| H11 | H5 plus only Dot.finish Array.map | 11,342 | 2,294 |
| H12 | H5 plus only Dot.finish fixed-array destructuring | 12,214 | 2,294 |

H11 meets the existing measured allowance while preserving every other C arithmetic body. Its artifact is `ca4dfbd90be40fbb97d72494fa2a8f399fac732482c10f92e9c82f6ee18a49bf`. Its source change reopens Std Array.map correspondence: the existing source-cut proof proves the four-coordinate reducer result against the retained state-threaded Array.map model, but not the actual Rust Std implementation. It cannot be adopted by relabeling that historical model proof. H8 meets the allowance with a substantially broader arithmetic re-pin.

H5/H12 avoids that new map boundary but is 214 CU above the owner's current allowance. H12's freshly rebuilt artifact is byte-identical to H5: `b5cb382b1738a016b2463d2388fd38523e55577bf8053b7b4f68aee482fa4d5b`. H7 is also artifact-identical to H5. Their fixture evidence is reused by byte identity rather than rerun.

The retained full OS-random-mask proof was separately verified against H5 and H11, using the same proof/public bytes and approved S4 artifact. H5 gives stage-1 delta12,214 and settlement delta2,299; H11 gives11,342 and2,299. Both preserve the exact checkpoint and return bytes and accept without errors. This is one retained full-mask sample, not a fresh randomness experiment or proof that cost is independent of every possible mask.

## Source and cache provenance

All builds use isolated source snapshots and the optimized cached SBF target, single job, capped MemoryHigh3GiB/MemoryMax4GiB/MemorySwapMax0. Receipts retain source inventories, commands, toolchain paths, wall time, process RSS, charged cgroup peaks and swap. Fixture scopes are separately capped. No production source or frozen proof candidate was modified.

H3's first attempt is retained under `H3-rejected`: copying source with old mtimes let Cargo reuse H2's library. Its measurements do not correspond to the intended source and are rejected. The corrected H3 and every later build touch only the isolated crate entry source mtimes and assert both library and program compilation lines. H1/H2 logs already show both crates compiled. Historical C, current-owned C and boxed D were also checked to show both crates compiled. Some cloned scope metadata contains an inherited manifest hash; the exact admitted source inventory and manifest hash in `gates/sbf/receipt.json` is authoritative.

The tail scanner traverses all bytes in original order and returns the original AccountAlreadyInitialized error on the first nonzero byte. A loop/byte refinement is still required before adoption. No validation check is stripped. H11 additionally needs the actual Std Array.map boundary discharged. H12 needs only its fixed-array destructuring re-pin beyond H5; its artifact identity is a measurement fact, not a source-equivalence theorem.

`summary.json` records each retained result and full-mask row. `check-candidates.py` checks the exact H11/H12 arithmetic deltas and the retained source hash inventories. No ELF, key, proof binary, olean, or other build artifact is committed.

## Focused map feasibility attempt, held

`map-feasibility/v2/` retains an exact current-H11 source cut with asserted `--include core::array` in the launch argv. Charon succeeds with actual Structured bodies for Array.map, try_map, try_from_fn, Drain.call_mut and Guard/drop machinery. It emits58 functions; this is extraction evidence only. Aeneas has not been run because lead direction prioritised the callback-free candidate and small independent mathematical checks. No extracted Rust Std refinement or actual pointer/drop correspondence is claimed. The initial v1 attempt omitted the include flag and is not evidence for map lowering; v2's explicit assertion and command receipt supersede it.
