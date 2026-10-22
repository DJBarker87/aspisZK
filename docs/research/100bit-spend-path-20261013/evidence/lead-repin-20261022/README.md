# Lead repin evidence, 22 October 2026

Stage 1 is a read-only exact-text/SHA-256 audit at source revision
25866ec331cc7ce27dd9956609c11d32fa8fa58a, after adoption 29cbab431.
Run `python3 -B docs/research/100bit-spend-path-20261013/evidence/lead-repin-20261022/check.py --check`.

`source-census.json` compares every original S10 frozen-source entry with this
checkout. `function-checks.json` separately compares every function in the
three adopted files with frozen b2727acd3. `pin-checks.json` groups explicit
locally resolvable tracked-file/item pins from the named lead evidence
scopes, retaining all contributing JSON receipts and input hashes. Old
intermediate attempts and experimental parser candidates are included; their
mismatches do not imply an adoption regression. Missing host files, cached
objects and ELF bytes are not asserted checked. Extraction manifests are
hashed as retained evidence, not regenerated for the adopted source.

No Lean, Rust, Kani, SBF, full regression or wallet operation runs here.
Existing formal receipts and axioms are reused at their original scope;
there are no new theorem/axioms claims. Stage 2 supplies ownership, adoption
impact and the report. Historical receipts remain immutable.

Stage 2 is complete in `REPIN.md`, `ownership.json`, `extraction-text.json`,
`artifact-pins.json` and `model-pins.json`. Stage 3's `validation.json` records
11 passing focused checks and resource metrics. `validate.py` reproduces the
source/hash validation and writes a new timed receipt; `impact.py --check`
checks deterministic evidence without changing it. Historical binary
references include linked artifacts; no new linked-artifact pin is inferred.
