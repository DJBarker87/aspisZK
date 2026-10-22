# Count-group domain correction

The retained `node_count_binary_group` requires
`well_formed(&level[..n])` on every call. That is sufficient locally but is
not an invariant of the in-place node_count loop.

Start with live indices `[0,1,2,3,100,101,200]`, n=7. Three groups consume
(0,1), (2,3), (100,101), writing parents at slots 0,1,2. The actual scratch
prefix is now `[0,1,50,3,100,101,200]`, i=6, w=3. The full prefix is not
strictly increasing (50 > 3), while the unread suffix `[200]` is valid.
The fourth actual group therefore does not satisfy the old certificate's
precondition. This is a certificate-domain gap, not a source counterexample.

`node_count_unread_group` checks the unchanged frozen source count_group
under `well_formed(&level[i..n])`, n<=16, i<n, w<=i. It proves exact i/w
advancement, supplied-sibling contribution and every scratch coordinate.
It passes universally, including arbitrary already-consumed scratch.
The source body and shipped crates are unchanged.

The corresponding logical while consumes the equal-parent prefix of the
unread list. `MultiproofConeCountGroups.drop_group` proves exactly one or
two occupied children under strict order. `source_level_eq` identifies the
source-shaped group scan with frozen countLevel. `MultiproofConeCountLevels`
proves parent order and `count_eq` for arbitrary height, hence height 18,
without any digest/oracle-value premise. `MultiproofConeCountPhysical.rows_projection` now supplies the in-place
written-prefix/unread projection. `MultiproofConeCountPhysicalLevels` composes
it through height, preserves the unread gate domain and identifies the result
with nodeCount. `SlotTail.slot_count_eq` consumes that physical count directly;
the source-shaped logical recurrence is no longer substituted as an assumed
count in the accepted slot tail. CountBounds proves the full count at most
288, so accumulating the contributions cannot overflow usize. The retained
P6 boundary is the local Kani-to-Nat-memory interpretation; source/caller
carrier binding remains separate.
