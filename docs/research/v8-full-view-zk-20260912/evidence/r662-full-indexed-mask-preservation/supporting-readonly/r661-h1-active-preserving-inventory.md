# R661 H1 active-preserving inventory (read-only)

Scope: source/model map for a possible H1-preserving correction. This is not a
privacy conclusion, a source-correspondence result, or a rank claim.

## TwoSwap model table

`lean/AspisV8R19/TwoSwapSourceTable.lean`
SHA-256 `88bedf159e0cf288d514f59c734e8af6f6c42252c9875e02d67d330a0eaa87e7`.

* `baseNat`/`backNat` are the arithmetic permutation at lines 10--38.
* `order` is `swap 127 1023`, then `swap 126 1021`, then `base` (lines 40--42).
* `isInactive` and `inactive` are aliases of the generated T163 table (lines
  43--44); the pivot is 1023 and is inactive (lines 46--47).
* The exact table is `lean/AspisV8R19/T163SourceTable.lean`, SHA-256
  `6aaf8bc2e1fce9a5a0116eac8eda44b5ca2032e5dcb5d2824587e05bf8ff3795`:
  literal `inactiveBlocks` starts at line 7, `isInactive` is the block lookup
  at lines 12--13, and `inactive` is its filter over all 1024 coordinates at
  line 51. It proves permutation and pivot facts, but no cardinality theorem.

The frozen audit calls its noninactive coordinates `active` and asserts 214;
thus it has 810 inactive coordinates by the 1024 universe, but this count is
an audit assertion rather than a Lean cardinality theorem for the TwoSwap
alias.

## Frozen 562-row H1 diagnostic matrix

Frozen source:
`/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/docs/research/v8-no-work-100-20260907/experiments/r17_c1_witness_audit.rs`
SHA-256 `1aa5c416fd971bb65bf5fd7aab20046a6e13c171dbaf272674337682f57f1a13`.

Lines 36--51 construct `active = {r | !map.inactive[r]}`, assert its length is
214, and allocate a `562 x 1022` matrix. For each unit source column:

| rows | value |
|---|---|
| 0--213 | `m[r]` at each active coordinate, where `m = map.inverse(chord(qvector(unit, abc), abc))` (41--42) |
| 214 | inactive-coordinate sum of `m` (43) |
| 215--302 | 88 raw fibre dots with `chord` (44) |
| 303--305 | 3 point dots with `m` (45) |
| 306--561 | 256 `primal(q, alpha)` values (46) |

The target has only the raw, point and final portions populated: negative dots
against `map.forward(h0)` at 49--50 and negative scaled primal values at 51.
The later diagnostic selects active+balance+final rows, lines 52--74. This is
an audit program, not a proof that its `map` is the Lean TwoSwap table or that
these equations are the selected verifier's universal legal-witness relation.

## Existing formal material

No inspected theorem supplies a basis in the kernel of all 214 H1 active rows.
The closest reusable generic interfaces are:

* `AspisV8R19/H1RelationLift.lean` SHA-256
  `78b39fc4c91010719b7468dd1bad12becb36476241a3687d8c7d6fd7b639fe1c`:
  `certificate_lift` (lines 10--16) requires a supplied `A (v i)=0` for each
  basis vector; `affine_repair` (20--27) likewise requires `A pad=0`.
* `AspisV8R17/WitnessShear.lean` SHA-256
  `93e145db116ee4861242699cd4c2cce4bd3eedf2df83d42b5b9cd82be44edf1e`:
  `witness_shear_same_uniform_law` (49--60) requires `gv (dg c h)=0` for
  every prefix/coin pair, plus its separate shared-observation equality.
* `AspisV8R17/AffinePosterior.lean` SHA-256
  `17a34bfdbac2340908a37f01f747d187037cf9018b68f5191b6244780c85c0df`:
  `joint_affine_same_uniform_law` (68--89) requires explicit H coverage,
  consistency and compatible G coverage. It does not provide them.
* `AspisV8H1C2/HelperObservation.lean` SHA-256
  `80be141f671cd0d40bc5b62958a419e56bca3f98ce66b5698a02b40535ef9f63`:
  `fixed_helper_observation_uniform` (15--32) needs matching, pole freedom,
  and a supplied linear-map coverage equality.
* `AspisV8R17/RawFinalCoverage.lean` SHA-256
  `89192f147ff136b485eb2d42c2d7523e1100bcc5c84811c9335f7324b511d53d`:
  `compatible_raw_final_coverage` (27--74) deliberately excludes H1 active
  restrictions (file comment lines 4--6).

`ActiveEntry`/`ActiveLinearForm` only normalize degree/linear-form algebra for
three generic chord components; they do not establish active-row kernel facts.

## R657 comparison and missing bridge

`lean/AspisV8R19/R657CompleteResidualRepair.lean`, SHA-256
`0c71a7655177cbedbb2d44bc82a38f96cf05af16d42027342cc7d94b9c943ec4`, proves
for its 13-column AugmentedQuotient combination: seven ordinary relations,
seven structured relations, two retained points, 271 sparse coins, 22-by-4
query roots, 32 first folds, and inactive balance (lines 21--41). It has no
active-coordinate predicate or conclusion.

Its `actualMask` is exactly the inverse transport of `SourceMaskTransport.code`
(`R645TwoSwapHighDirections.lean`, SHA-256
`d197c2e10925fdccec9e837ed54cabade4a5ac713e559e16a2815fd759bb7f87`, lines
19--20). `actual_mask_balanced` proves only the inactive sum is zero (39--43),
and `actual_selected_coins_zero` proves only 271 reads (45--50). The defining
`SourceMaskTransport` comment explicitly says active coordinates are allowed
to change (lines 5--7, SHA-256
`879ffe2c022feb57b6dc77c34719527f4f195e04532bd803fb12651cb5a655e4`).

Therefore R657 does **not** establish that its correction vanishes on all 214
active rows. A universal concrete nonzero counterexample cannot be stated from
these symbolic files alone: R657 remains parameterized by field, chord data,
roots and chosen target, and it may be zero for some choices. The smallest
literal active-row candidate in the Lean table is index 11 (`inactiveBlocks`
entry 11 is `false`); for any nonpivot row the definition reduces the mask
coordinate to `code ... (order.symm row)` (BalancedTransport lines 58--62).
No existing theorem evaluates that R657 AugmentedQuotient combination to a
nonzero value at this or any active row. Establishing either all-active
preservation or a valid instantiated counterexample needs a new bridge from
this model table and correction family to the H1 active map.

The next missing proposition is thus an actual active-row kernel/basis theorem
for the complete 214-coordinate H1 observation map, with an explicit binding
to the frozen source table and its legal-witness target. It is not supplied by
the low 13-direction R657 repair.
