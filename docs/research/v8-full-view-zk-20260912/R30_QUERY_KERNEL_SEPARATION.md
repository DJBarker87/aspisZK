# R30: separate the large coordinate blocks from query repair

Parent `5cf16f1796e14d8d05aa485b0a7d6ca86f5b27df` (R29).
Branch `research/v8-r30-query-kernel-separation-20260928`.

**Result:** the retained R17 raw/final kernel argument applies to the current
T163/sparse-G coordinate blocks. A normalized high-coordinate section makes
the 214 active-row and 271 G-coordinate matrices independent of the query
factor. At both actual prefixes their ranks are 214 and 271; the remaining
query-dependent row increments have ranks **8 and 13** respectively.

These are still fixed-prefix lower-rank certificates, not a universal rank
or privacy theorem. The protocol, verifier, selected proofs and mask sources
are unchanged. No source challenge or query is replaced, and no old H1
semantic schedule search or unrelated regression is repeated.

## Reusing the kernel rather than rediscovering it

The retained `RawFinalKernel.lean` characterizes zero raw values and zero
Final256 by divisibility of the three nonconstant channel polynomials by
the distinct-query root polynomial

```
P(t) = product over 22 query fibres of (t-root).
```

The channel A is determined by the zero fold:
`A=-alpha B-alpha^2 C-alpha^3 D`. The retained `ChordBalance.lean`
separates the one nonbalanced top direction, leaving 699 balanced directions
with B,C,D degrees at most 254 and all three high quotient entries zero.
Those existing mathematical results are reused, not recompiled as an
unchanged full regression. Their source natural-basis correspondence remains
an explicit obligation rather than an automatic Rust extraction claim.

For each natural-basis degree d=22..254, the new checker uses the triangular
family `P*t^j` to compute the remainder R_d of the unit basis polynomial E_d.
The corrected polynomial `E_d-R_d` vanishes at every actual query root and
has **exactly the same coefficients at degrees 22..254 as E_d**. The remainder
has degree below 22. Each of the three nonconstant quotient channels therefore
gives one kernel direction whose only difference from the direct high unit
lies in quotient coordinates 0..87.

This normalized section is more useful than comparing only the ranks of
two matrices: it identifies their large coordinate blocks column-for-column.
All 699 directions are checked for raw/final/OOD zeros, balance and legal
high-tail shape. This does not label every direction a legal H1 pad; the
active-row equations still have to be imposed.

## Current layout and the low-support boundary

The original R17 active-query ledger's minimum active code coordinate was
100. **Under the selected T163 map it is 91.** Do not reuse that old numeric
layout premise unchanged. Sparse G reads 271 code coordinates starting at
128 and ending at 938.

The actual chord product of a quotient supported in 0..87 is supported in
0..90. The checker enumerates all **88 input coordinates × three chord
axes = 264** basis products and checks their support, all active original
rows, all sparse G coins and acceptance by the actual H1-padding API.
The observed maximum is exactly 90. Thus the low repair remains invisible
to both large coordinate blocks, but the active-row separation is now tight.

The two complete current-source kernel checks each verify:

- 699 normalized kernel directions;
- **339,015** coordinate equalities between corrected and direct high units;
- **61,512** raw zero values, plus all final, balance and OOD checks;
- 233 source-natural-basis remainders against all 22 actual roots;
- an explicit negative control showing the ordinary point observation
  **does change** under low repair. Point/relation residuals cannot be dropped.

No arbitrary “good query schedule” is chosen. Input bytes are the same
accepted public prefixes already retained in R27–R29.

## Remaining row systems

The raw/final/balance constraints are built into the 699-column section.
The current retained observations reduce to:

| Map | Query-independent core | Additional rows | Tested added rank | Total tested rank |
|---|---:|---:|---:|---:|
| H1 | 214 active rows | 3 point + 7 ordinary-polynomial | 8 | 222 |
| G | 271 sparse coins | 3 point + 7 ordinary + 7 structured-polynomial | 13 | 284 |

The checker performs incremental row elimination with the core first, so
the reported rank increments refer to the residual rows after eliminating
the core. It records the pivot columns. This is not a claim that only 8/13
field operations are needed or that the corresponding ranks are universal.
The core matrices still depend on alpha, chord and the fixed layout; only
their query-root dependence has been separated. The residual matrices retain
the semantic challenges, point weights and both relation polynomials.

The 222/284 ranks agree with the full R28/R29 ranks after accounting for the
322 compatible raw/final dimensions and one balance dimension:
`545-323=222`, `607-323=284`. This accounting is a consistency check, not a
replacement for the executed core/residual eliminations.

## New symbolic support proof

`LowKernelSeparation.lean` **imports the existing R17 SourceScatter model**.
Its five new theorems prove:

1. If every scatter edge moves an input at most one index upward, support
   below n moves to support below n+1.
2. Low quotient support below 88 makes the even chord coefficients zero
   at parity index 46 and above.
3. The odd coefficients are zero at parity index 45 and above.
4. Hence every interleaved chord coefficient at index 91 or above is zero.
5. Two quotient functions agreeing from coordinate 88 onward have identical
   chord observations from coordinate 91 onward.

These quantify over arbitrary values and chord coefficients, using symbolic
support/linearity, not reduction of large concrete recurrences. The scatter
edge-growth condition is explicit; the retained Rust bit-loop/field/index
correspondence and concrete layout binding are not magically discharged by
the generic theorem. The complete source basis checks above provide current
executable evidence for that finite support component.

All five new `#print axioms` results contain only `propext` and `Quot.sound`.
The unchanged SourceScatter prerequisite was compiled once because its object
was absent in this NUC cache; its 19 audits contain only the standard
propext/Quot.sound/Classical.choice set. No `sorryAx` or new security premise.

## Execution receipts

Base revision as above. Cached NUC Rust release/offline/locked/jobs 2 with
overflow checks enabled; heavy work is the named core/residual elimination.
Rust scope 5 GiB high / 7 GiB max / zero swap. Focused Lean 4.31 scope 2/3 GiB,
zero swap. No SBF build, proof regeneration, full formal manifest or unchanged
runtime suite was needed for this host-only source/proof change.

| Exact target | Exit | Wall | Peak RSS (KiB) | Swaps |
|---|---:|---:|---:|---:|
| Kernel-checker release compile | 0 | 19.63 s | 516,244 | 0 |
| Current source kernel, world0 | 0 | 0.99 s | 15,288 | 0 |
| Current source kernel, world1 | 0 | 0.99 s | 15,372 | 0 |
| SourceScatter missing-object restoration | 0 | 1.65 s | 1,677,940 | 0 |
| LowKernelSeparation five leaves | 0 | 1.52 s | 1,658,996 | 0 |

The first formal runner lacked Lean's explicit source-root option when
emitting an object outside the cached project. It exited 1 in 0.62 s,
RSS 798,664 KiB, swap 0, before theorem compilation. Adding `-R` fixed the
runner; the failure is retained and not counted as proof.

Evidence: `evidence/r30-query-kernel/`; verify with

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r30_evidence.py
```

## Next proposition and a concrete route

Prove appropriate lower bounds for the two direct core maps as functions of
alpha/chord, then the residual compatible-image bounds with their query
dependence retained, or give source-justified exception bounds. The present
two finite ranks do not establish these propositions.

For G, the direct projection is especially structured: selected coordinate
`128+3*i` lies in a four-slot block, with at most two selected positions in
any block. At the *algebraic* chord `(1,0,0)`, selecting the corresponding
nonconstant slot for a nonzero local slot, and slot 1 for a selected local
slot 0, suggests independent one/two-row blocks. The only paired selected
positions within a block are 0 and 3. At alpha=1 the proposed blocks have
form `[[-1,-1],[0,1]]`, whose square is identity. This is a proposed next
nonvanishing certificate route, **not an executed source-valid OOD experiment
or an already compiled determinant result**. Its source column indexing and
normalized-circle polynomial restriction must be checked before use.

The full privacy goal still additionally requires posterior-preserving
adaptive construction, coherent pre-beta extraction, shared-oracle/seed/
commitment correspondence, retries/publication and explicit losses. C1's
negative result, fixed-block hiding and these coordinate arguments remain
separate. No CU saving is claimed: the selected verifier stays at
**1,620,236 / 1,621,719 CU**, with the actual 1M gate open.
