# R724 shifted null covector: chord-transpose omitted-pair check

This follows the all-code residual vector from
[`all-code-pullback-result.json`](all-code-pullback-result.json) through the
literal source `chord_transpose` arithmetic from the saved frozen
[`r17_opening_weights.rs`](source-pins/r17_opening_weights.rs), with
`abc = (7, 5, -5)` over M31.

For every `(d,s)`, it evaluates the exact functional on the diagnostic pair
`pair(d,s,7) - pair(0,s,7)` as:

```
Lq[4*d+s] - 7^s Lq[4*d] - Lq[s] + 7^s Lq[0]  (mod 2147483647).
```

Validation: all 241 recorded matrix columns evaluate to zero (there are 234
distinct pair coordinates because the saved column list contains duplicates).

Searching `d=22..254`, `s=1..3`, outside those recorded coordinates finds 59
nonzero pairs.  The first is **`(47,3)`**, with exact M31 value
**`1909084209`**.  The complete list is in
[`chord-transpose-omitted-pairs-result.json`](chord-transpose-omitted-pairs-result.json).

This is a mechanical direction check only.  It shows the current covector
does not annihilate every pair in that larger family; it does not give a
privacy, rank, source-execution, or cryptographic conclusion.

Command: `python3 check_chord_transpose_omitted_pairs.py` (exit 0).

| Artifact | SHA-256 |
| --- | --- |
| script | `905bfe2e480ad3cad4380af828928b1e0a9924bfea0fedd749f3402627f26f5a` |
| result | `2a158fd33280c7eb72233eae1a1b2b61543e2ce7f64ec281f9a1af1973b51827` |
| all-code residual input | `f217aaeacfd7ae4d8177ca585ff0342dac8b3fef34dfe8a641e7e96a21266aa4` |
| raw recorded-column list | `5b2589052d7138fae11c6f780551ab70192aec3a03a1435cd8fea2f915601a4e` |
| frozen source transpose | `cfe40c2743b2df43222469cdc853fcbd88b745deba77ab12ed92ccc871a51afc` |
