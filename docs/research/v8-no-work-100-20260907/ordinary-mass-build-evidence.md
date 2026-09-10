# Ordinary mass: four-leaf checkpoint checked

This is new evidence for source parent
`15700387af1d52af4b7ddff8de92541ec2891ff2`; previous sampler, causal and
higher-Y checkpoint bytes remain frozen. The inherited runner retains its
creation pin `289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

All four leaves are green: FiniteOptionMass v1 (two audits), OrdinaryRawMass
v2 (six), OrdinaryPrefixMass v2 (six), and NestedCircleRouting v3 (ten).
The final checkpoint has 24 standard-only axiom audits, eight retained
attempts, four successful attempts and four failed diagnostics. All eight
attempts have zero swaps. The transfer receipt resolves 93 exact artifact
versions with zero unmapped artifacts; historical versions at one remote
pathname remain distinguished by their hash.

| Target / attempt | Exit | Wall seconds | Peak RSS KiB | Release audits |
| --- | ---: | ---: | ---: | ---: |
| FiniteOptionMass v1 | 0 | 2.99 | 6695656 | 2 |
| OrdinaryRawMass v1 | 1 | 2.73 | 6696156 | — |
| OrdinaryRawMass v2 | 0 | 2.98 | 6730072 | 6 |
| OrdinaryPrefixMass v1 | 1 | 5.32 | 6721052 | — |
| OrdinaryPrefixMass v2 | 0 | 3.54 | 6741872 | 6 |
| NestedCircleRouting v1 | 1 | 3.38 | 6658852 | — |
| NestedCircleRouting v2 | 1 | 3.39 | 6658732 | — |
| NestedCircleRouting v3 | 0 | 3.64 | 6692524 | 10 |

The first raw attempt needed an explicit finite instance for the named
Skeleton. Prefix v1's broad list simplification was replaced with symbolic
`List.ofFn_mul` and quotient/remainder steps. Nested v1/v2 failed local
syntax, Option-bind and layout-guard projection steps; explicit status/guard
splitting fixed the final version. No failed attempt is release evidence,
including any temporary `sorryAx` emitted after elaboration failure. The
successful FiniteOptionMass log retains its benign unused-Nonempty warning;
no cosmetic replay was made. All exact failed sources, logs and manifests
are retained, without inverse-edit reconstruction.

Two authorized metadata-only appends supplied exactly three missing local V7
source/output pairs. The base manifest moved 794→798→800; earlier per-run
manifests and green-state snapshots stayed unchanged. The separate raw and
decoder cache audits check all retained bytes, borrowed source pins and exact
boundary variants. Historical cache trace audits receive no new theorem
credit. See `ordinary-raw-cache-review.md` and `ordinary-decoder-cache-review.md`.

All current access uses Tailscale `dombarker@100.108.41.90`; `nuc.local` is
only the host-key alias. All eight focused proof receipts show Lean `-j1 -M9500`,
MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPU quota 200%, the literal
executed command, GNU time resources, exact source/output hashes, unchanged
pre/post imported bytes and terminal exits/resources. Green leaves have
standard-only axiom audits. Proof depth stayed 200 throughout; Prefix declared
250000 heartbeats before its first attempt, and all other leaves declared
200000. Neither limit was raised on retry. This auditor performs no
compiler launch, package rebuild, remote action or old theorem-suite replay.

The mathematical endpoint remains scoped: unconditional raw-word and actual
one-call block-decoder mass keep aborts in the coin space. The total block
correspondence preserves rounded block discard and canonical value decoding.
NestedCircleRouting proves status projections, actual consumed-tail cuts,
hard-failure abort and halted-padding prerequisites. This is not yet the
whole nested-controller/source refinement, actual nested tape law, adaptive
two-OOD law, source/Fiat–Shamir coupling, checked payment extraction or full-view
privacy theorem. No global error number or additional repair charge is assigned.

Final read-only verification commands:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/ordinary-mass-audit.py --prepare-receipt
python3 docs/research/v8-no-work-100-20260907/experiments/ordinary-mass-audit.py --check-recorded
```

The first emits transfer metadata and is not itself a release pass. The second
checks the complete scoped record and must fail if any source, output,
imported artifact, attempt, resource contract or document pin changes.

Final source/output pairs are recorded in full in `ordinary-mass-evidence.json`:

- FiniteOptionMass: `6c16346bcb927d736076242c0f78dee84c8c58b3f77dd92aaa752f3dd7216ff2` / `3635c0dd8d0798b8bb8c2c26157f509a66e7946c052503adf4414f623d75eb03`.
- OrdinaryRawMass: `172912af296a875e9b6f2087bf9a155b2f51a6568f74c75cc96c0266a7da643e` / `527764acacfcd9df1cc6102738c09b80ff5597c3994d3035b5d318190a800358`.
- OrdinaryPrefixMass: `0874301b24962ef2034936305ad6e611edc865d1943facabeb17e99c32edf9ce` / `d01815aa917bab68ecb2361bec2db4117ac9e758281a940454655a4c9a2c4632`.
- NestedCircleRouting: `632a8bdd960b67d62c97b1b49926f5113a910aaf74d6bbe21976efb19c2c2836` / `61bd96ba4e2c30c90bbca4e632b0ef0e730ca27f86ef4630150817340305ec38`.

Green run manifests contain 859, 865, 869 and 871 entries respectively. The
auditor traverses their actual research/V7 import closures (81, 189, 197 and
11 source/output artifacts respectively). The inherited initial 794-artifact
snapshot is also byte/git-checked, including retained pinned source fallbacks;
concurrently modified main pathnames are not borrowed. Native mathlib/package
artifacts remain a declared pinned-revision cache boundary, not a rebuilt or
replayed package release. Old checkpoint verification is read-only byte/source
verification, with no new theorem credit.
