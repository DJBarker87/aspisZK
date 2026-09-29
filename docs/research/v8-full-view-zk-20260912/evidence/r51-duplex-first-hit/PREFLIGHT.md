# R51 resource and failed-preflight record

Base: `e5d3c322dd27c3c90b5b486a4ceea9db74564d2e`.
NUC reached through Tailscale at `100.108.41.90`.
Read-only preflight reported 62 GiB total, 46 GiB available and only
`init.scope` running. Existing system swap usage was 7.5 GiB; the task
scopes prohibit new swap and each target's `time -v` record reports zero.

All Lean scopes `aspis-r51-lean-{a,b,c,d,e,f,g,h,i}` used
`MemoryHigh=3G MemoryMax=5G MemorySwapMax=0 TasksMax=128`, serially.
They reused R50's 257-object pinned cache, then each focused predecessor.
Two missing unchanged dependencies were compiled in d; no package build.

Source scopes `aspis-r51-source-{a,b}` used
`MemoryHigh=5G MemoryMax=7G MemorySwapMax=0 TasksMax=128`.
Expected time was compilation of the new release control binary, not
proof generation or dense elimination. The release runner used offline,
locked, two-job Cargo and retained overflow checks. Peak possible combined
reservation with one Lean scope was 12 GiB, below the available memory.
There were no resource kills or increased caps.

## Failures retained

- Lean a: small list-membership/length proof errors; fixed by explicit
  empty-list simplification and symbolic `omega` arithmetic.
- Lean c: missing `AdaptiveOracle.olean` in this cache. Added the two exact
  local dependency targets, not a cold package build.
- Lean f/g: elaboration tried to normalize concrete finite 32-byte-state
  membership and reached the recursion limit. No limit increase. Replaced
  that proof by a generic finite-type injection/cardinality lemma and only
  instantiated its finished result with the concrete state type.
- Lean h: the generic proof needed explicit `Finset.mem_coe`; fixed locally.
- Source a: the inherited runner expected 196 control manifest entries.
  Read-only inspection found 197: the selected control already included
  the R42 query target. The assertion fired before staging or compilation.
  The new wrapper now expects exactly 197 and still verifies every hash.
  It retains the parent manifest hash `646739cf819e1aa263e2b734bc4f1e9335fc23d6b4051ef51c84028b7a235f6a`.
  Terminal result was exit 1 / `AssertionError` at the inherited manifest
  length assertion; no source-a binary or stage was produced.

Successful source b: compile 18.62 s, peak RSS 519,256 KiB; control execution
0.00 s at reported timer precision, peak RSS 2,112 KiB. Both exit 0, swap 0.
Successful logs retain pre-existing dependency warnings. Lean success logs
retain harmless unused-simp warnings; no extra replay was run for cosmetics.
