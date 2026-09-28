# R24 follow-up: measured whole-program arithmetic

2026-09-28. Follows pushed `2ee34c1591fbdc6663fdb8529e559ba2eb14a675`.
Same two frozen R19 proofs, sparse G, T163, transcript, wire format and checks.
No auxiliary proof, protocol redesign, settlement or deployment.

## Complete runs, not kernel extrapolations

| Candidate | World 0 CU | World 1 CU |
|---|---:|---:|
| Prior R24 C | 1,817,965 | 1,819,559 |
| Prepared-multiplier guarded product (D) | 1,734,341 | 1,736,011 |
| D + simple checked dot (simple-dot A) | 1,704,310 | 1,705,674 |
| Also inline fast multiply (simple-dot B; rejected) | 1,713,454 | 1,714,868 |
| **D + simple dot + flattened reconstruction (simple-dot C)** | **1,690,509** | **1,691,993** |

The selected v0 endpoint is simple-dot C, approximately **41.0% below R20**.
Another approximately **40.9%** reduction is still needed to meet 1M.

All listed full candidates compiled without SBF frame diagnostics, accepted
both complete honest proofs under the diagnostic cap, passed all 3,281 host
wire controls, and rejected the corrupted final through a checked error at
the diagnostic cap. **Both genuine proofs still exhaust at the actual 1M
cap.** No resource failure is described as checked rejection.

Prepared multipliers reconstruct the original value from their private first
two component pairs and use the existing guarded canonical product. Source
inspection finds only the private constructor populating those components;
the original fallback remains for noncanonical inputs. The focused field gate
now also compares prepared products against the unmodified R20 implementation:
603,888 canonical result comparisons plus the retained raw/invalid-constructor
controls. Native arbitrary/basis/genuine-input gates remain unchanged.

The simple dot retains equal-length and 4,096-term bounds and explicitly
checks all four limbs of every operand before multiplication. It replaces
the former private nine-channel accumulator, not canonical parsing or a
cryptographic check. Tests compare the actual old adapter with the new adapter
on 576 vectors (lengths 0 through 4,096, including maximum canonical limbs),
7,272 noncanonical cases and two length errors. The old implementation is
retained as a source-pinned oracle. The full stage has 179 pins, including
the new differential source, original adapter copy and host Cargo manifest.
An initial 178-pin runner preflight rejected this stage before compilation;
inspection identified that newly pinned manifest and corrected the exact
count to 179. No pin was waived.

Inlining only the fast multiplication path, while outlining the untouched
fallback, avoids the prior branch-range/stack failure. It passes correctness
and native runtime gates and saves roughly 3.7k native scalar CU. **The full
verifier is nevertheless slower by 9,144/9,194 CU.** It is not selected.

## Complete executed-instruction evidence

The D world-0 trace accepts at exactly the clean **1,734,341 CU**, executing
1,627,468 SBF instructions. Its unstripped symbol artifact has byte-identical
`.text` to the deployed-to-simulator ELF; this is not a guessed symbol map.

| Exclusive compiled function | Instructions | Entries |
|---|---:|---:|
| QM31 multiplication | 342,679 | 2,269 |
| Private whole-dot adapter | 165,215 | 65 |
| Packed beta combination | 161,818 | 22 |
| Opening-channel caller | 113,165 | 1 |
| Scalar ordinary caller | 61,902 | 1 |
| Nine-channel reconstruction closure | 50,698 | 654 |

Inline work remains attributed to its caller; these are exclusive instruction
counts, not complete inclusive function CU. Total loads/stores are 437,943
instructions, shifts 252,544, moves 274,824 and integer multiplications 72,302.
The CU/instruction difference includes runtime/syscall work; the trace does
not establish that any whole category can be removed.

The trace justified re-testing simple dot after the scalar product became
cheaper. It did not justify keeping the isolated inlining win. The new driver
reuses the locked tracing dependency set and the actual full R20 transaction
builder, fixing only its four-argument `--micro` selector for one honest run.
The complete traced CU is checked against the unchanged clean driver.

## Separate ISA experiment

The same D source built with cached platform-tools v1.54 `--arch v3` and the
same LiteSVM driver accepts at 1,733,806/1,735,494 CU, only 535/517 below v0.
It also fails the actual 1M cap. This does not solve the budget problem and
is not installed as the control. No live-cluster deployability is claimed.
Architecture/feature availability is distinct from local execution; see the
[Solana sBPFv3 overview](https://solana.com/es/upgrades/sbpfv3-programs).

## Linear reconstruction experiment

After reducing nine arbitrary u64 channels to canonical residues a through i,
the same extension-field reconstruction has limbs

```
a + 3d - b - e - f
c + 2f - a - b - d - 3e
g + b + e - h - a - d
i + a + b + d + e - g - h - c - f
```

Adding respectively 3P, 6P, 3P and 4P makes the staged unsigned evaluation
nonnegative; every intermediate is below 10P < 2^35. The existing reducer then
canonicalizes each limb. The original channel reductions are unchanged, so
this rewrite needs no canonicality premise on the input u64 channels.

`R24Reconstruction.lean` proves the generic commutative-ring identity and
small numeric bounds: exit 0, 1.38s, RSS 1,669,912KiB, swap 0, Lean 4.31 cached
workspace. Axioms are only `propext`, `Quot.sound`, and (for numeric bounds)
`Classical.choice`; no `sorryAx`. This is not a full source/machine refinement.

The actual field gate adds dot arities 2, 3 and 4, giving **1,207,776** canonical
comparisons, plus the existing raw/fallback checks. The non-inlined native
candidate is stack-safe and passes all controls at 283,695/283,739 scalar CU
versus 284,643/284,684. The variant based on the slower inline layout was
stopped after host checks; it was not misreported as an SBF result.
Composed with the simple dot but without fast-path inlining, it saves another
13,801/13,681 CU in complete executions. The full host wire/dot gates and
stack-safe SBF gate pass. The two actual 1M executions still exhaust.

## Boundary and retention

The under-1M target and the pre-existing full privacy/soundness obligations
remain open. These are unchanged-protocol execution optimizations only.
Focused arithmetic lemmas do not close transcript, shared-oracle, extraction,
retry or publication obligations.

`collect_r24_followup.py` retains exact sources, manifests, compile/runtime
logs, trace hashes/attribution and rejected measurements under
`evidence/r24-followup/`. Large trace registers, ELF files and keys stay on
the NUC; no keys are deleted or committed. The Solana testing skill's
source gate → stack-safe SBF → full LiteSVM cadence remains in force.
All jobs use the previously recorded swap-disabled capped scopes and cached
release/offline toolchains. No unrelated work or production path is changed.
