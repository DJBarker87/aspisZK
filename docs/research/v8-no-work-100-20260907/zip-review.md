# Review of the supplied structured-weight ZIP

Reviewed `/Users/dominic/Downloads/aspis_v8_branch_review.zip` on 2026-09-07.
SHA256: `53d586271e9ca976f65a544168338d51cbdd5c26fc1f7d2581d220294604c475`.
The package reviews this research branch at f773b014. All six entries were
inspected before execution: regular files, 23493 uncompressed bytes, no links
or path traversal. Extraction and script output writes stayed in a new temporary
directory. The original ZIP was not modified. No package contents were uploaded.

## Verdict

**No correctness defect found in the reviewed product-component contraction.**
The two-bit transfer treats the actual non-separable dual folds correctly.
The package's arithmetic and operation-count outputs reproduce byte-for-byte.
Its caveats correctly distinguish algebra, conditional security models and CU.

This closes the specific concern that a product component must be expanded to
1024 coefficients to perform chord transport followed by four dual folds. It
does not close arbitrary grouped-mask handling, source acceptance/refinement,
extraction, hiding, or complete-transaction CU parity.

## What was independently verified

- All five entries in SHA256SUMS passed before execution and again after both
  scripts regenerated their JSON outputs.
- Arithmetic: 40282-byte canonical q22 model; 39934 packed model; exact q21/q22/q23
  binomial probabilities and query-plus-semantic subtotals reproduced.
- Merkle counts follow `internal = 2*(queries+frontier-1)`:
  selected q16/cap203 gives 436, q22/max296 gives 634. Leaves are 32 and 44.
  The +198 internal and +12 leaf hashes are real extra work, not a percentage
  prediction for full transaction CU. The package hardcodes the baseline
  headline count, but the independent structural identity confirms it.
- The package's 1026 carry checks, 16 local block basis cases and 40 complete
  product-component cases passed. The reproduced counts are exactly 4440/4105
  generic products/base scalings for its reference and 163/47 for its fast path.
- A separate adapter compared 40 full-dimension cases, all four terminal outputs,
  between the package's dense path, its fast path, and Rust using the pinned
  production QM31 kernel. All 160 field outputs agreed, including zero product
  factors, zero chord coefficients, and zero/one/minus-one fold challenges.
  This addresses the package's stated limitation that its two Python paths
  share the same independently implemented field model.

## Code review details

`structured_chord.py:87` correctly implements the carry transfer. With source
and target block digits j,r and a carry entering the low bit, its three entries
are the identity contraction, the sum of terminating carry paths, and the one
carry-through-both-bits path. Checking all 16 local basis pairs is meaningful:
these entries are bilinear, so local basis equality determines the operator.

`structured_chord.py:120` splits the first dual block by the y input bit, pairing
entries (0,2) and (1,3) for the first line bit. This is the right low-bit-first
circle convention. It does not incorrectly split all four dual entries into
two rank-one factors.

`structured_chord.py:125` handles y multiplication through the identity
`y*(A+yB) = yA + (1-x²)B`, with x²=(1+T2)/2. Its negative carry term has the
correct sign. `structured_chord.py:138` contracts remaining blocks in reverse
order with the upper carry boundary dropped, matching projection into W.

The truncated `xt` reference is also correct here: it retains the intermediate
513th coefficient for X², and omitted output weights represent zero padding
beyond the original space. This is not an unchecked omission of live values.

No fixes to the supplied package are needed for these identities. Before a
verifier port, add an explicit adapter from the production big-endian stored
Product/Tensor/Multilinear factor order to the low-bit-first array (reverse the
factor array once, then test it against source `weight_at`). Do not silently
treat Grouped64x16 or Dense as a single product component. These are integration
obligations already acknowledged by the package, not newly discovered bugs.

## Additional Rust simplification: 91 products

The independent Rust `block_terminal` shares all three lower block transfers
across the four terminal outputs, specializes the final one-hot block, and
defers the common four factors of 1/4 to one factor 1/256. It counts 87 generic
QM31 products, including challenge-power preparation, or **91 including the
four outer-scale products**. All four actual dual folds are covered, unlike
the earlier rank-one-only scalar experiment.

This count was independently compared with the ZIP via `zip_crosscheck.py`,
not inferred from its claimed 163. Multiplication counts are syntactic: additions,
halvings, indexing, allocations, parsing, transcript and other verifier work are
not included. The Rust dense control is 3072+1020+8=4100 generic products before
input materialization, versus the package's 3072+1360+8=4440: its dual fold uses
four generic products per chunk while the Rust reference uses three plus
halvings. These are different reference implementations, not contradictory counts.

The savings versus an unoptimized **new** dense chord transform do not establish
savings versus selected V7, which has no such transformation. No full-CU speedup
factor should be attached to 4440/163 or 4100/91.

## Reproduction and measured scope

Use a freshly extracted, inspected copy of the ZIP. From its directory:

```sh
shasum -a 256 -c SHA256SUMS.txt
/usr/bin/time -l python3 arithmetic_check.py
/usr/bin/time -l python3 structured_chord.py
shasum -a 256 -c SHA256SUMS.txt
```

From the research worktree:

```sh
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/chord_link.rs -o /tmp/aspis-v8-chord-link
python3 docs/research/v8-no-work-100-20260907/experiments/zip_crosscheck.py /path/to/extracted/aspis_v8_branch_review /tmp/aspis-v8-chord-link
```

Observed Apple M3/macOS runs, all exit 0 and zero swaps:

| Check | Wall time | Maximum RSS |
|---|---:|---:|
| Package arithmetic | 0.09 s | 17317888 B |
| Package structured tests | 1.38 s | 20086784 B |
| Cross-language 40 cases | 1.54 s | 22904832 B |

These are small finite arithmetic checks, not heavy elimination/proof-generation
gates. No SBF build, deployment, full prover or full privacy proof was executed.

## Security status after this review

The ZIP's diagnosis of the extraction gap is sound. Since its f773b014 snapshot,
this run has produced explicit counterexamples to an unconditional 28-gamma
recovery bound; see [recovery-counterexample.md](recovery-counterexample.md).
The 99.246-bit boundary applies to the isolated same-support recovery event,
not the full accepted-proof event. The ZIP does not claim otherwise and does
not supply the missing joint extraction theorem. Its useful engineering result
should be retained independently of that security problem.
