# R752 source-only plan: remaining SCC left inverses

This is a source generator and focused finite-certificate proof effort. SCC 4 and all 39 other generated blocks compiled green; all 40 blocks excluding separately handled SCC 6 now have literal Lean left-inverse certificates. No source-execution or security result is claimed.

## Inputs and accounting

- Certificate: `.r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json`
- Certificate SHA-256: `d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4`
- The certificate records 41 SCCs. SCC 6 has dimension 39 and 1,521 diagonal cells; it is already handled separately by R747–R751 and is skipped here.
- The other 40 blocks have maximum dimension 16 and total 1,627 diagonal cells. Their row proofs are split into 59 chunks, no chunk exceeding four rows.
- The generated blocks are SCC indices 0–5 and 7–40. The first maximum-size block selected for review is SCC 4 (dimension 16); SCCs 9, 12, and 39 are also dimension 16.
- The certificate serializes each matrix value as four M31 limbs. The generator rejects nonzero higher limbs, emits limb 0 into `ZMod 2147483647`, and checks the supplied `B_times_A` values are exactly the identity in all four limbs. This formatting/checking step performs no matrix multiplication or elimination.

## Proposed Lean proof shape

For each SCC, one matrix module defines the literal `A_scc` and `B_scc` matrices. The row modules state one scalar theorem per product cell, using the same successful bounded route as R747/R750:

```lean
simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
  Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
norm_num <;> decide
```

Each row theorem assembles its cell facts after `fin_cases j`. A block module assembles all rows with `ext i j` and `fin_cases i`, then invokes the existing `Matrix.isUnit_det_of_left_inverse` and `Matrix.det_ne_zero_of_left_inverse`. As in R751, the local closed `Fact (1 < 2147483647)` supplies the library's `Nontrivial (ZMod P)` instance; this adds no theorem premise. Intended axiom footprint is the standard `[propext, Classical.choice, Quot.sound]`, subject to actual compilation and audit.

Files are under `generated/scc-NN/`. `generate.py --check` verifies the input certificate pin, expected original input-matrix hash, serialized identity entries, exact generated source, and absence of extra Lean source files. The current generator SHA is `4d7985d77310f7a3aa3c23de02136dd939fe735fbc5ecc4f4bbb50c527fbbd83`; `generated/SHA256SUMS` SHA is `de7cbbe4fff18efc2fc4c72eaf1493244cd6ef921226a8f3600d2d4bf8d64ebe`.

## First 16×16 review target

SCC 4 source files and hashes:

- `generated/scc-04/R752SCC04Matrix.lean` — `e796fcee5cb48d11b4f2f460a683b8c48ea15c9a8312ceac0ef1c13855d157bf`
- `generated/scc-04/R752SCC04Rows01.lean` — `4aaea2f8657ac886d939967eb1679a3b70ac2e0cd99510372910ca29bd663a06`
- `generated/scc-04/R752SCC04Rows02.lean` — `ef5f01cc299f111470a96fbd52142390a16a7cc614f3f18ed595f099255a6e2a`
- `generated/scc-04/R752SCC04Rows03.lean` — `b621570428f817c3ef23fd186bca90be44f477dfef09a263abefad034cd44089`
- `generated/scc-04/R752SCC04Rows04.lean` — `471d4b534df5a01dc86037cd80de888e3ef460f4aa476f09a2792e2fdf38c2b3`
- `generated/scc-04/R752SCC04Inverse.lean` — `a979d1a90cbbf5862b237a3d97905a6a04210768947029ffae8ec73da3690bd9`

The generated source imports use `AspisV8R19.R752...` so the focused runner can stage modules at the package namespace. SCC 4 compiled sequentially (matrix, four row chunks, aggregate); complete receipts and result table are in `SCC4_STATUS.md`. The other 39 blocks completed the same sequential focused process. Exact attempts, complete axiom reports, source hashes, logs, receipts, and cached olean hashes are indexed in `R752_SUCCESS_INVENTORY.json`; the earlier SCC 4 failure remains in that inventory.

## R751 cached dependencies

The R751 green run loaded these R750 source modules (source hashes from their saved files) and cached `.olean` files from `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib/AspisV8R19/`:

| Module | Source SHA-256 | Cached `.olean` SHA-256 |
|---|---|---|
| R750JointBlock39Rows01 | `a2b17b84d57e4f35fed24e822ca50186cd177a4dee0ce8f3c33b16030fa5ef52` | `5b64d77b161a01ab28d836c25babd1e59eabad7937d374987ed28a43252aed30` |
| R750JointBlock39Rows02 | `e081bf94f1d5a11349eebc263c859d5f301d71bfcd359fc29ee990a87eab447d` | `beacdc65f964d74724ee45e2441acd82362d40a56a086e48f91662bd68187bb6` |
| R750JointBlock39Rows03 | `c17098337197039a35d78107b962b15acbec975a4d85f620822886d2337619c9` | `3b62362c1f5d3eaf61d144a3afaf70c3ec2fecd9b17eb9454d210d0a70abd86b` |
| R750JointBlock39Rows04 | `69efc42b1da9920faec4fd19615fc46741443ac697da4445e651b538d5dc8e2b` | `d10bc63be7bd90c730134246f754aa02304eabd0e2d09346ba28db7a1da95e5b` |
| R750JointBlock39Rows05 | `82d583f97f68eb5bea7af6268ac0136525450851051ad1a213b9d026af8b9cb7` | `2d05831c5c85996bb7c576e4d8743c14c34b0436cb33e10f580d008246f03520` |
| R750JointBlock39Rows06 | `1fa09dfd70e4e986a7afc6bc89436d48584fe6b3eb6318df5f2a5229928b72ee` | `7fc3596d817fc592a089ee3fb0447a02934cca35583332fb5116ecb9d4cac521` |
| R750JointBlock39Rows07 | `1fc64ab3c2d6d1890f0fc6b123d057019c340a85b1257207493fd340947b8347` | `f2039b14ea36b6c456c4bbd2e5e64aad37f7e1c99d073809207ef13b71f8c1eb` |
| R750JointBlock39Rows08 | `d8e905c5f88318f9fbe2d7b413383abffd1ba8b57fb5396ea640dfff662934af` | `49ceb0570a1158656c56af6af0a1d113604acd1d9a42191df262c331ef1387df` |
| R750JointBlock39Rows09 | `28a42d58697f211d07ca1e4fbe83b37ca2ca9965628c2a5f6f1f6bd74d3c77df` | `e3bd47377c53cbb9909aaf11b4cbdb7d7ca2f90fb4eb2de3cab075b60dcc440a` |
| R750JointBlock39Rows10 | `390e538b4560bdc2a424a251e272cbd7f24f4a6678f17516629ed5e048dbe1d3` | `e898d7c4321134c6088720e29e4cec39989b5db31bb7aa6196c5f9d418fcffa2` |

R751 itself compiled successfully at run `1791143104938765000` (exit 0, wall 1.42s, RSS 3,371,896 KiB, swap 0) with both theorem reports `[propext, Classical.choice, Quot.sound]`.
