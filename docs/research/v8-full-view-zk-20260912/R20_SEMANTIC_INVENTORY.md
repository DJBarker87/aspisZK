# R20 semantic-terminal source inventory (read-only)

This is a source inventory of the canonical-a copy on the NUC, not a
correspondence or security conclusion. No source/build files were changed.

Canonical source root:
`/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/aspis-r19-canonical-20260921-a`

Inspected files and SHA-256:

- `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`:
  `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`
- `docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs`:
  `6d815512fd45210f360edb1ab6d52c7748db4c652d236097de5b3fb63a8b9bf1`

## Actual semantic execution path

`performance_verifier.rs:33-68` performs ten semantic rounds (`r=0..9`),
each reading `w.v[1+27*r .. 1+27*(r+1)]`, constructing a 28-coefficient
polynomial (`poly[0]=sent[0]`, `poly[2..]=sent[1..]`, and the boundary
coefficient at `poly[1]`), absorbing the round record at line 51, sampling
`s.z[r]` at line 52, and evaluating at lines 53-54. It then builds 84 terminal
claims at line 57 and calls `payment_terminal` once at line 58. The optional
`v8_semantic_control` block calls the entire terminal a second time at lines
61-66; that is a diagnostic duplicate, not a default path. `verify_parsed`
calls `semantic` at line 125, then `prepare_compact` at 128 and the primary
relation verifier at 131. The non-primary/reference branch repeats semantic
and preparation at lines 137-145.

`pair_forest_semantic_terminal.rs:1241-1274` is the terminal composition:
three opened rows and mask-only claims are selected at 1241-1251; selectors
are evaluated at 1253; Poseidon is evaluated at 1254; `semantic_packed` at
1256; the Copy component at 1258-1266; then semantic lanes and Poseidon lanes
are folded in reverse with the same `theta` at 1267-1274. Thus the common
opened segment for semantic/digest work is `openings.z` (16 QM31 values), with
`succ_z`/`xor12_z` additionally used by path/range/occupancy logic.

## Event inventory: literal digest path

The literal public-digest implementation is `public_digest_lanes` at
`pair_forest_semantic_terminal.rs:609-694`; every event calls
`add_digest_binding` (`364-378`), which emits all 8 digest lanes using one
selector and one expected `Digest`.

Fixed events, all reading `openings.z[0..8]`, are:

| Source lines | Event | Selector/local | Condition/tweak |
|---|---|---|---|
| 615-622 | anchor | `row(56*16+11)` / local 11 | always |
| 623-630 | nullifier | `row(26*16+11)` / local 11 | always |
| 631-640 | recipient | `row(29*16+11)` / local 11 | only `public.recipient=Some` |
| 641-648 | change | `row(32*16+11)` / local 11 | always |
| 674-681 | next root | `row(53*16+11)` / local 11 | always |

The append loop at lines 652-673 has exactly 20 level events, block
`34+level`:

- bit 0 at `((source.next_pair_index >> level)&1)==0`: selector
  `row((34+level)*16)`, opened offset `RATE`, expected
  `empty_root(level)`, `right_tweak=true`; line 375 adds
  `MERKLE_NODE_COMPRESSION_V3_TWEAK` to the final digest limb.
- bit 1: selector `row((34+level)*16+12)`, opened offset 0, expected
  `source.frontier[level]`, no tweak.

The carry event at lines 682-691 is optional: `carry=min(trailing_ones,20)`;
when `carry<20`, selector `row((33+carry)*16+11)`, offset 0, and expected
`after.next_frontier[carry]`. For carry 20 there is no carry digest event.
Therefore the literal digest count is 24 events without a recipient/carry,
25 with exactly one optional event, and 26 with both. Each event has 8 lane
residuals and the same opened array; only selector, expected digest, offset,
and the empty-root tweak differ.

`public_digest_packed_row_major` (`734-819`) repeats the same event inventory,
rows, branch conditions, offsets, expected roots/frontier values, and tweak,
but packs four residual lanes into each of two outputs (`714-723`). It is an
alternative cfg path, not an additional default execution.

## Existing selector-tensor factoring and safe reference candidates

The selector-tensor path (`1026-1105`) already groups the exact events into
three destination locals and contracts with `low[0]`, `low[11]`, and
`low[12]` at lines 1095-1104:

- local 0: all 20 append-level events (`1067-1075`),
- local 1: anchor, nullifier, optional recipient, change, next root, and
  optional carry (`1032-1060`, `1077-1093`),
- local 2: the second append-level output (`1067-1076`).

`append_levels_packed_selector_tensor` (`948-975`) loops exactly 20 times,
passing `frontier[level]`, `opened`, and `selector_high[34+level]` to
`append_level_packed_selector_tensor` (`887-941`). Its branch and tweak are
identical to the literal inventory. `optional_carry...` (`982-1009`) emits
two packed outputs only for carry `<20`; otherwise zero.

Potential by-reference candidates are strictly mechanical and require caller
equivalence review: `left_digest_packed_selector_tensor` currently takes
`opened:[QM31;16]` and `expected:Digest` by value (`826-830`); the optional
recipient helper takes `opened` and recipient digest by value (`855-859`);
append-level takes `frontier:Digest` and `opened:[QM31;16]` by value
(`887-892`); append-levels takes `frontier:[Digest;20]`, `opened`, and
`selector_high:[QM31;64]` by value (`948-952`); optional carry takes
`opened` and `frontier` by value (`982-987`). The public wrapper already
passes `&openings`/`&selectors`; changing these helper signatures is only a
candidate after preserving exact semantics and checking emitted code.

The literal and row-major paths already use references for openings and
selectors (`609-613`, `734-738`). No claim is made that by-value arguments
are physical copies after optimization.

## Other semantic lane duplication/counts

- Schedule: `add_schedule_lanes` (`382-391`) emits 16 initial lanes and 16
  absorption lanes. Initial selector construction and domain/length tweaks
  are at `241-312`: domain constants are `DOMAIN_OWNER_KEY`,
  `DOMAIN_NOTE`, `DOMAIN_NULLIFIER` (`273-276`); lengths are 8, 18, and 16
  (`277-282`). Variant selectors at `219-238` distinguish private transfer
  and withdrawal.
- Absorption has three lane classes: lanes 0-1 use `fixed`, lanes 2..RATE-1
  use `fixed+chunk_two`, and lanes RATE..15 use
  `fixed+chunk_two+chunk_eight+nodes` (`315-359`). The factored audit path
  precomputes these three prepared scales (`345-358`).
- Path: `add_path_lanes` (`394-410`) has one common selector from
  `sum_high(57..63) * (low[1]+low[5]+low[9]+low[13])`; `path_lanes_literal`
  (`412-427`) emits 17 lanes: one bit term plus 8 empty-branch and 8
  occupied-branch transitions. The factored path (`430-463`) uses the same
  17 outputs and selectors.
- Value/range: `add_value_lanes` (`466-519`) uses three value selectors at
  locals 0,2,4 of the value-auxiliary block; it computes 30 quadratic
  residuals (10 each for z/succ_z/xor12_z), 3 reconstruction residuals
  (`497-502`), and 2 conservation residuals (`513-518`), writing packed
  lanes at 49 and 82. The range selector is their sum (`471-477`).
- Occupancy: `occupancy_lanes_literal` (`557-578`) emits 12 lanes: 3 scalar
  terms, 8 digest lanes (`571-573`), and one variant-sensitive final term
  (`574-576`). It uses `both=input_occupancy+output_occupancy`; the factored
  path (`580-605`) reuses occupied/empty selectors but preserves all 12
  outputs. `expected_output` is 1 for private transfer and 0 for withdrawal
  (`521-526`).

## Transition/domain controls

`validate_transition` (`180-209`) requires pool and deployment-domain
equality, `sequence == next_pair_index`, capacity bound, and
`after.next_pair_index == source.next_pair_index+1` (`183-191`). It checks all
20 frontier levels. For each level, `carry=min(trailing_ones,20)`; the carry
level is skipped when `carry<20`, lower levels expect the canonical empty root,
and remaining set-bit levels expect the source frontier (`193-207`). These
conditions must remain part of any factoring comparison; the digest helper's
carry branch is not the whole transition check.

## Duplication counts visible in source

These are source execution/event counts, not CU claims:

1. Ten semantic rounds per `semantic` call; the diagnostic
   `v8_semantic_control` adds one complete second terminal call.
2. The non-primary/reference verifier branch (`performance_verifier.rs:134-145`)
   invokes semantic and preparation a second time; the primary-only path
   returns at line 133.
3. One default terminal composition contains one `semantic_packed`, one
   Poseidon projection, one Copy evaluation, and 25-27 digest events
   depending on recipient/carry. The row-major and selector-tensor digest
   implementations are cfg alternatives, not additive counts.
4. The selector-tensor append helper executes 20 level calls per terminal;
   each call emits exactly two packed output groups, one of which is zero for
   the selected branch.
5. The semantic lane builder emits 16 schedule + 17 path + 33 range + 2
   conservation + 12 occupancy + either 8 literal digest lanes or 2 packed
   digest groups, before the later Poseidon/Copy composition fold.

No architectural transformation, premise weakening, CU estimate, or security
closure is inferred from this inventory.
