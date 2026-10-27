# Authorized records extraction repairs (D274 and D275)

Entry revision: 9128568ac068bee9527806edc32982a35010c706.

1. In `records`, pair_forest_copy_builder.rs:229, verbatim:

```diff
-    let pair = &input.pair;
+    let pair = input.pair;
```

This copies the identical immutable value instead of retaining a shared borrow.
`PoolV1PairInputNoteWitnessV1` derives `Clone, Copy` at
`crates/aspis-statement/src/pool_v1/pair_trace.rs:71` (type declaration at 72).
No signature/type or other function change. Existing `raw(&pair.field)` calls
continue to borrow the same field values from this copy. 

2. D275 (widening D274), inside `records` only, verbatim:

```diff
-    for level in 0..24 {
+    let mut level = 0;
+    while level < 24 {
         let (bit, sib) = if level == 0 {
             (u32::from(pair.selected_second), other)
         } else if level <= 20 {
             (((pair.membership.index >> (level - 1)) & 1) as u32, pair.membership.siblings[level - 1])
         } else {
             (u32::from(input.super_root_directions[level - 21]), input.super_root_siblings[level - 21])
         };
         bits[level] = bit;
         sibs[level] = raw(&sib);
+        level += 1;
     }
```

Authorized kind (iii): identical body, bounds 0 inclusive and 24 exclusive,
index type `usize`, and ascending iteration order. The increment occurs after
the body, which has no `continue` or `break`; it cannot overflow (last increment
is 23 to 24). Removes the range iterator's unsupported `ub_checks<bool>` without
changing recorded values. No Copy premise is required for this loop repair;
repair 1's Copy derive remains `pair_trace.rs:71`. No other function, signature,
or type changed. Diagnostic extraction must determine whether this is the last
source repair; all three ELFs will then be rebuilt once.

3. D275 kind (i), inside `records` only, verbatim:

```diff
+    let input = *input;
     let pair = input.pair;
```

Replace the shared parameter borrow's uses with an identical entry copy;
`PoolV1PairForestInputNoteWitnessV1` derives `Clone, Copy` at
`crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:53` (type at 54).
All field accesses now use that immutable copy. No argument needs a new `&`:
only field values are read from `input`. The signature remains unchanged.
This targets the next shared-loan failure in the loop branch at records:237–241,
`InterpBorrows.ml:2731`, recorded by `pv14-records-aeneas-02`. No body, bounds,
iteration order, output, other function, signature, or type changes.

Final D275 source revision: `c58e0473ac60090f016a59e3b7953f429de2d5c2`.
Entry-copy repair 3 retained in the LLBC but did not clear the branch-join
blocker. No further repair applied. See `BLOCKER-D275.md` and its explicitly
unapplied branch restructuring proposal; final ELF results are reported in
`REPORT-D275.md` / `gate-a-d275.json`.

4. D277, branch-local stores inside `records` only, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index abe6c1e3cb..bc02764afb 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -233,15 +233,18 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let mut sibs = [[0u32; 8]; 24];
     let mut level = 0;
     while level < 24 {
-        let (bit, sib) = if level == 0 {
-            (u32::from(pair.selected_second), other)
+        if level == 0 {
+            bits[level] = u32::from(pair.selected_second);
+            sibs[level] = raw(&other);
         } else if level <= 20 {
-            (((pair.membership.index >> (level - 1)) & 1) as u32, pair.membership.siblings[level - 1])
+            bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
+            let sib = pair.membership.siblings[level - 1];
+            sibs[level] = raw(&sib);
         } else {
-            (u32::from(input.super_root_directions[level - 21]), input.super_root_siblings[level - 21])
-        };
-        bits[level] = bit;
-        sibs[level] = raw(&sib);
+            bits[level] = u32::from(input.super_root_directions[level - 21]);
+            let sib = input.super_root_siblings[level - 21];
+            sibs[level] = raw(&sib);
+        }
         level += 1;
     }
     let empty = pair_empty_roots();
```

For each level 0..23, the same branch is selected. Level 0 writes the
selected-second bit and `raw(other)`; levels 1..20 write the same shifted
index bit and `raw(membership.siblings[level - 1])`; levels 21..23 write
the same super-root direction and sibling. Each iteration writes exactly
one bits cell and one sibs cell at the same level before the same increment.
The earlier tuple evaluated its bit before its sibling; the new branch stores
the bit before loading the sibling. The bits index is always below 24; all
source sibling indices are in bounds (0..19 or 0..2), so this introduces no
new panic and removes none. `raw` is unchanged; no allocation or I/O is added.
Sibling digests are Copy arrays of M31 (`M31` derives `Clone, Copy` at
`crates/aspis-core/src/field.rs:22`; digest is `[M31; 8]`). Existing pair and
forest Copy justifications remain `pair_trace.rs:71` and
`pair_forest_trace.rs:53`. No signature, type, other function or file of
shipped code changes.

5. D277, split the three disjoint level ranges to eliminate sibling branch
joins (repair 4 still failed at records:239–247, InterpBorrows.ml:2731).
Verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index bc02764afb..928de21956 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -231,20 +231,19 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
     let mut bits = [0u32; 24];
     let mut sibs = [[0u32; 8]; 24];
-    let mut level = 0;
+    bits[0] = u32::from(pair.selected_second);
+    sibs[0] = raw(&other);
+    let mut level = 1;
+    while level < 21 {
+        bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
+        let sib = pair.membership.siblings[level - 1];
+        sibs[level] = raw(&sib);
+        level += 1;
+    }
     while level < 24 {
-        if level == 0 {
-            bits[level] = u32::from(pair.selected_second);
-            sibs[level] = raw(&other);
-        } else if level <= 20 {
-            bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
-            let sib = pair.membership.siblings[level - 1];
-            sibs[level] = raw(&sib);
-        } else {
-            bits[level] = u32::from(input.super_root_directions[level - 21]);
-            let sib = input.super_root_siblings[level - 21];
-            sibs[level] = raw(&sib);
-        }
+        bits[level] = u32::from(input.super_root_directions[level - 21]);
+        let sib = input.super_root_siblings[level - 21];
+        sibs[level] = raw(&sib);
         level += 1;
     }
     let empty = pair_empty_roots();
```

The write order remains level 0, levels 1..20 ascending, levels 21..23
ascending. Every bit, sibling expression and raw call is identical at each
level. Both loops terminate with level 24; arithmetic and all array accesses
are in bounds, preserving all panic/abort behavior. No allocation, I/O,
signature, type or other function changes. Copy locations remain
`field.rs:22`, `pair_trace.rs:71`, `pair_forest_trace.rs:53`.

6. D277, expand the fixed path/frontier/root loops, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 928de21956..31ccec3879 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -233,19 +233,52 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let mut sibs = [[0u32; 8]; 24];
     bits[0] = u32::from(pair.selected_second);
     sibs[0] = raw(&other);
-    let mut level = 1;
-    while level < 21 {
-        bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
-        let sib = pair.membership.siblings[level - 1];
-        sibs[level] = raw(&sib);
-        level += 1;
-    }
-    while level < 24 {
-        bits[level] = u32::from(input.super_root_directions[level - 21]);
-        let sib = input.super_root_siblings[level - 21];
-        sibs[level] = raw(&sib);
-        level += 1;
-    }
+    bits[1] = ((pair.membership.index >> 0) & 1) as u32;
+    sibs[1] = raw(&pair.membership.siblings[0]);
+    bits[2] = ((pair.membership.index >> 1) & 1) as u32;
+    sibs[2] = raw(&pair.membership.siblings[1]);
+    bits[3] = ((pair.membership.index >> 2) & 1) as u32;
+    sibs[3] = raw(&pair.membership.siblings[2]);
+    bits[4] = ((pair.membership.index >> 3) & 1) as u32;
+    sibs[4] = raw(&pair.membership.siblings[3]);
+    bits[5] = ((pair.membership.index >> 4) & 1) as u32;
+    sibs[5] = raw(&pair.membership.siblings[4]);
+    bits[6] = ((pair.membership.index >> 5) & 1) as u32;
+    sibs[6] = raw(&pair.membership.siblings[5]);
+    bits[7] = ((pair.membership.index >> 6) & 1) as u32;
+    sibs[7] = raw(&pair.membership.siblings[6]);
+    bits[8] = ((pair.membership.index >> 7) & 1) as u32;
+    sibs[8] = raw(&pair.membership.siblings[7]);
+    bits[9] = ((pair.membership.index >> 8) & 1) as u32;
+    sibs[9] = raw(&pair.membership.siblings[8]);
+    bits[10] = ((pair.membership.index >> 9) & 1) as u32;
+    sibs[10] = raw(&pair.membership.siblings[9]);
+    bits[11] = ((pair.membership.index >> 10) & 1) as u32;
+    sibs[11] = raw(&pair.membership.siblings[10]);
+    bits[12] = ((pair.membership.index >> 11) & 1) as u32;
+    sibs[12] = raw(&pair.membership.siblings[11]);
+    bits[13] = ((pair.membership.index >> 12) & 1) as u32;
+    sibs[13] = raw(&pair.membership.siblings[12]);
+    bits[14] = ((pair.membership.index >> 13) & 1) as u32;
+    sibs[14] = raw(&pair.membership.siblings[13]);
+    bits[15] = ((pair.membership.index >> 14) & 1) as u32;
+    sibs[15] = raw(&pair.membership.siblings[14]);
+    bits[16] = ((pair.membership.index >> 15) & 1) as u32;
+    sibs[16] = raw(&pair.membership.siblings[15]);
+    bits[17] = ((pair.membership.index >> 16) & 1) as u32;
+    sibs[17] = raw(&pair.membership.siblings[16]);
+    bits[18] = ((pair.membership.index >> 17) & 1) as u32;
+    sibs[18] = raw(&pair.membership.siblings[17]);
+    bits[19] = ((pair.membership.index >> 18) & 1) as u32;
+    sibs[19] = raw(&pair.membership.siblings[18]);
+    bits[20] = ((pair.membership.index >> 19) & 1) as u32;
+    sibs[20] = raw(&pair.membership.siblings[19]);
+    bits[21] = u32::from(input.super_root_directions[0]);
+    sibs[21] = raw(&input.super_root_siblings[0]);
+    bits[22] = u32::from(input.super_root_directions[1]);
+    sibs[22] = raw(&input.super_root_siblings[1]);
+    bits[23] = u32::from(input.super_root_directions[2]);
+    sibs[23] = raw(&input.super_root_siblings[2]);
     let empty = pair_empty_roots();
     let w = RW {
         input_value: pair.value,
@@ -268,24 +301,50 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
         transfer: rec.is_some(),
         asset: asset.0,
         next_pair_index: snapshot.next_pair_index,
-        frontier: {
-            let mut frontier = [[0u32; 8]; 20];
-            let mut l = 0;
-            while l < 20 {
-                frontier[l] = raw(&snapshot.frontier[l]);
-                l += 1;
-            }
-            frontier
-        },
-        empty: {
-            let mut roots = [[0u32; 8]; 20];
-            let mut l = 0;
-            while l < 20 {
-                roots[l] = raw(&empty[l]);
-                l += 1;
-            }
-            roots
-        },
+        frontier: [
+            raw(&snapshot.frontier[0]),
+            raw(&snapshot.frontier[1]),
+            raw(&snapshot.frontier[2]),
+            raw(&snapshot.frontier[3]),
+            raw(&snapshot.frontier[4]),
+            raw(&snapshot.frontier[5]),
+            raw(&snapshot.frontier[6]),
+            raw(&snapshot.frontier[7]),
+            raw(&snapshot.frontier[8]),
+            raw(&snapshot.frontier[9]),
+            raw(&snapshot.frontier[10]),
+            raw(&snapshot.frontier[11]),
+            raw(&snapshot.frontier[12]),
+            raw(&snapshot.frontier[13]),
+            raw(&snapshot.frontier[14]),
+            raw(&snapshot.frontier[15]),
+            raw(&snapshot.frontier[16]),
+            raw(&snapshot.frontier[17]),
+            raw(&snapshot.frontier[18]),
+            raw(&snapshot.frontier[19]),
+        ],
+        empty: [
+            raw(&empty[0]),
+            raw(&empty[1]),
+            raw(&empty[2]),
+            raw(&empty[3]),
+            raw(&empty[4]),
+            raw(&empty[5]),
+            raw(&empty[6]),
+            raw(&empty[7]),
+            raw(&empty[8]),
+            raw(&empty[9]),
+            raw(&empty[10]),
+            raw(&empty[11]),
+            raw(&empty[12]),
+            raw(&empty[13]),
+            raw(&empty[14]),
+            raw(&empty[15]),
+            raw(&empty[16]),
+            raw(&empty[17]),
+            raw(&empty[18]),
+            raw(&empty[19]),
+        ],
     };
     (w, p)
 }
```

Repair 5 clears the branch join but leaves loop-context matching failure at
records:237–242, InterpJoin.ml:2209. Each expanded path pair writes exactly
the former loop's bits[i] and sibs[i], in the same ascending order for
i=1..23; level 0 is unchanged. The frontier and empty literals evaluate
the same raw calls at indices 0..19 in ascending order, returning the same
20-element arrays. Removed loop counters are unobservable and never overflow.
All literal indices and shifts are within their original bounds; raw and
pair_empty_roots calls remain unchanged. There is no new panic/abort,
allocation or I/O; no signature, type or other function changes. Copy
locations remain field.rs:22, pair_trace.rs:71, pair_forest_trace.rs:53.

7. D277, consume the recipient option once, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 31ccec3879..5914874afd 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -280,6 +280,10 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     bits[23] = u32::from(input.super_root_directions[2]);
     sibs[23] = raw(&input.super_root_siblings[2]);
     let empty = pair_empty_roots();
+    let (recipient_owner, recipient_salt, transfer) = match rec {
+        Some(r) => (raw(&r.owner_key), raw(&r.salt), true),
+        None => (ZERO8, ZERO8, false),
+    };
     let w = RW {
         input_value: pair.value,
         output_value: out,
@@ -292,13 +296,13 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
         pair_occupied: pair.pair_leaf.second_occupied.0,
         pair_second: raw(&pair.pair_leaf.second_commitment),
         pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
-        recipient_owner: match rec { Some(r) => raw(&r.owner_key), None => ZERO8 },
-        recipient_salt: match rec { Some(r) => raw(&r.salt), None => ZERO8 },
+        recipient_owner,
+        recipient_salt,
         change_owner: raw(&chg.owner_key),
         change_salt: raw(&chg.salt),
     };
     let p = RP {
-        transfer: rec.is_some(),
+        transfer,
         asset: asset.0,
         next_pair_index: snapshot.next_pair_index,
         frontier: [
```

Repair 6 clears loops; Aeneas then rejects the second rec match at
records:295:42–43, InterpExpansion.ml:290. For Some(r), the same owner
and salt raw calls produce the same words and transfer=true. For None,
both are ZERO8 and transfer=false. Both raw calls move before the witness
record's other raw calls; raw only reads eight fixed in-bounds M31 fields,
with no panic, abort, allocation, mutation or I/O, so the order is unobservable.
The empty-root call remains first. No types/signatures/other functions change.
No new Copy is required; M31 Copy derive remains field.rs:22.

8. D277, copy the remaining immutable borrowed records, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 5914874afd..32cc1f8ae3 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -227,6 +227,8 @@ include!("../../../../docs/research/v8-r0-zk-20261009/refine/diffharness/tests/g
 fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
            chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
     let input = *input;
+    let chg = *chg;
+    let snapshot = *snapshot;
     let pair = input.pair;
     let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
     let mut bits = [0u32; 24];
@@ -281,7 +283,10 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     sibs[23] = raw(&input.super_root_siblings[2]);
     let empty = pair_empty_roots();
     let (recipient_owner, recipient_salt, transfer) = match rec {
-        Some(r) => (raw(&r.owner_key), raw(&r.salt), true),
+        Some(r) => {
+            let r = *r;
+            (raw(&r.owner_key), raw(&r.salt), true)
+        },
         None => (ZERO8, ZERO8, false),
     };
     let w = RW {
```

Repair 7 reaches raw(&r.salt) but fails at records:284:24–36,
InterpBorrowsCore.ml:629. The Some branch now reads both digest fields from
an identical local Copy of r. Change-note and snapshot reads likewise use
identical immutable local copies. PoolV1OutputNoteWitnessV1 derives Clone,
Copy at payment_relation.rs:88; PoolV1PairLiveSnapshotV1 at
pair_tree_profile.rs:403. No value, branch, raw call order, panic/abort,
allocation, I/O, signature, type, or other function changes.

9. D277, return recipient digests from the match before raw projection,
verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 32cc1f8ae3..57975db2a8 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -282,13 +282,12 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     bits[23] = u32::from(input.super_root_directions[2]);
     sibs[23] = raw(&input.super_root_siblings[2]);
     let empty = pair_empty_roots();
-    let (recipient_owner, recipient_salt, transfer) = match rec {
-        Some(r) => {
-            let r = *r;
-            (raw(&r.owner_key), raw(&r.salt), true)
-        },
-        None => (ZERO8, ZERO8, false),
+    let (recipient_key, recipient_note_salt, transfer) = match rec {
+        Some(r) => (r.owner_key, r.salt, true),
+        None => ([M31(0); 8], [M31(0); 8], false),
     };
+    let recipient_owner = raw(&recipient_key);
+    let recipient_salt = raw(&recipient_note_salt);
     let w = RW {
         input_value: pair.value,
         output_value: out,
```

Repair 8 still fails on the Some branch raw borrow at records:287:20–22,
InterpBorrowsCore.ml:629. Some(r) copies the same two digest values; raw
then projects them in the same order after the branch. None supplies two
all-zero M31 arrays, whose raw results are exactly ZERO8; its two added raw
calls only read fixed in-bounds fields and cannot panic, abort, allocate,
mutate or perform I/O. Thus the returned records and all observable behavior
are unchanged. Digest elements are Copy via field.rs:22; note Copy derive
is payment_relation.rs:88. No signature/type/other-function change.

10. D277, expand raw projection at its 72 call sites inside records,
verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 57975db2a8..63b88b2ca0 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -234,124 +234,124 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let mut bits = [0u32; 24];
     let mut sibs = [[0u32; 8]; 24];
     bits[0] = u32::from(pair.selected_second);
-    sibs[0] = raw(&other);
+    sibs[0] = [other[0].0, other[1].0, other[2].0, other[3].0, other[4].0, other[5].0, other[6].0, other[7].0];
     bits[1] = ((pair.membership.index >> 0) & 1) as u32;
-    sibs[1] = raw(&pair.membership.siblings[0]);
+    sibs[1] = [pair.membership.siblings[0][0].0, pair.membership.siblings[0][1].0, pair.membership.siblings[0][2].0, pair.membership.siblings[0][3].0, pair.membership.siblings[0][4].0, pair.membership.siblings[0][5].0, pair.membership.siblings[0][6].0, pair.membership.siblings[0][7].0];
     bits[2] = ((pair.membership.index >> 1) & 1) as u32;
-    sibs[2] = raw(&pair.membership.siblings[1]);
+    sibs[2] = [pair.membership.siblings[1][0].0, pair.membership.siblings[1][1].0, pair.membership.siblings[1][2].0, pair.membership.siblings[1][3].0, pair.membership.siblings[1][4].0, pair.membership.siblings[1][5].0, pair.membership.siblings[1][6].0, pair.membership.siblings[1][7].0];
     bits[3] = ((pair.membership.index >> 2) & 1) as u32;
-    sibs[3] = raw(&pair.membership.siblings[2]);
+    sibs[3] = [pair.membership.siblings[2][0].0, pair.membership.siblings[2][1].0, pair.membership.siblings[2][2].0, pair.membership.siblings[2][3].0, pair.membership.siblings[2][4].0, pair.membership.siblings[2][5].0, pair.membership.siblings[2][6].0, pair.membership.siblings[2][7].0];
     bits[4] = ((pair.membership.index >> 3) & 1) as u32;
-    sibs[4] = raw(&pair.membership.siblings[3]);
+    sibs[4] = [pair.membership.siblings[3][0].0, pair.membership.siblings[3][1].0, pair.membership.siblings[3][2].0, pair.membership.siblings[3][3].0, pair.membership.siblings[3][4].0, pair.membership.siblings[3][5].0, pair.membership.siblings[3][6].0, pair.membership.siblings[3][7].0];
     bits[5] = ((pair.membership.index >> 4) & 1) as u32;
-    sibs[5] = raw(&pair.membership.siblings[4]);
+    sibs[5] = [pair.membership.siblings[4][0].0, pair.membership.siblings[4][1].0, pair.membership.siblings[4][2].0, pair.membership.siblings[4][3].0, pair.membership.siblings[4][4].0, pair.membership.siblings[4][5].0, pair.membership.siblings[4][6].0, pair.membership.siblings[4][7].0];
     bits[6] = ((pair.membership.index >> 5) & 1) as u32;
-    sibs[6] = raw(&pair.membership.siblings[5]);
+    sibs[6] = [pair.membership.siblings[5][0].0, pair.membership.siblings[5][1].0, pair.membership.siblings[5][2].0, pair.membership.siblings[5][3].0, pair.membership.siblings[5][4].0, pair.membership.siblings[5][5].0, pair.membership.siblings[5][6].0, pair.membership.siblings[5][7].0];
     bits[7] = ((pair.membership.index >> 6) & 1) as u32;
-    sibs[7] = raw(&pair.membership.siblings[6]);
+    sibs[7] = [pair.membership.siblings[6][0].0, pair.membership.siblings[6][1].0, pair.membership.siblings[6][2].0, pair.membership.siblings[6][3].0, pair.membership.siblings[6][4].0, pair.membership.siblings[6][5].0, pair.membership.siblings[6][6].0, pair.membership.siblings[6][7].0];
     bits[8] = ((pair.membership.index >> 7) & 1) as u32;
-    sibs[8] = raw(&pair.membership.siblings[7]);
+    sibs[8] = [pair.membership.siblings[7][0].0, pair.membership.siblings[7][1].0, pair.membership.siblings[7][2].0, pair.membership.siblings[7][3].0, pair.membership.siblings[7][4].0, pair.membership.siblings[7][5].0, pair.membership.siblings[7][6].0, pair.membership.siblings[7][7].0];
     bits[9] = ((pair.membership.index >> 8) & 1) as u32;
-    sibs[9] = raw(&pair.membership.siblings[8]);
+    sibs[9] = [pair.membership.siblings[8][0].0, pair.membership.siblings[8][1].0, pair.membership.siblings[8][2].0, pair.membership.siblings[8][3].0, pair.membership.siblings[8][4].0, pair.membership.siblings[8][5].0, pair.membership.siblings[8][6].0, pair.membership.siblings[8][7].0];
     bits[10] = ((pair.membership.index >> 9) & 1) as u32;
-    sibs[10] = raw(&pair.membership.siblings[9]);
+    sibs[10] = [pair.membership.siblings[9][0].0, pair.membership.siblings[9][1].0, pair.membership.siblings[9][2].0, pair.membership.siblings[9][3].0, pair.membership.siblings[9][4].0, pair.membership.siblings[9][5].0, pair.membership.siblings[9][6].0, pair.membership.siblings[9][7].0];
     bits[11] = ((pair.membership.index >> 10) & 1) as u32;
-    sibs[11] = raw(&pair.membership.siblings[10]);
+    sibs[11] = [pair.membership.siblings[10][0].0, pair.membership.siblings[10][1].0, pair.membership.siblings[10][2].0, pair.membership.siblings[10][3].0, pair.membership.siblings[10][4].0, pair.membership.siblings[10][5].0, pair.membership.siblings[10][6].0, pair.membership.siblings[10][7].0];
     bits[12] = ((pair.membership.index >> 11) & 1) as u32;
-    sibs[12] = raw(&pair.membership.siblings[11]);
+    sibs[12] = [pair.membership.siblings[11][0].0, pair.membership.siblings[11][1].0, pair.membership.siblings[11][2].0, pair.membership.siblings[11][3].0, pair.membership.siblings[11][4].0, pair.membership.siblings[11][5].0, pair.membership.siblings[11][6].0, pair.membership.siblings[11][7].0];
     bits[13] = ((pair.membership.index >> 12) & 1) as u32;
-    sibs[13] = raw(&pair.membership.siblings[12]);
+    sibs[13] = [pair.membership.siblings[12][0].0, pair.membership.siblings[12][1].0, pair.membership.siblings[12][2].0, pair.membership.siblings[12][3].0, pair.membership.siblings[12][4].0, pair.membership.siblings[12][5].0, pair.membership.siblings[12][6].0, pair.membership.siblings[12][7].0];
     bits[14] = ((pair.membership.index >> 13) & 1) as u32;
-    sibs[14] = raw(&pair.membership.siblings[13]);
+    sibs[14] = [pair.membership.siblings[13][0].0, pair.membership.siblings[13][1].0, pair.membership.siblings[13][2].0, pair.membership.siblings[13][3].0, pair.membership.siblings[13][4].0, pair.membership.siblings[13][5].0, pair.membership.siblings[13][6].0, pair.membership.siblings[13][7].0];
     bits[15] = ((pair.membership.index >> 14) & 1) as u32;
-    sibs[15] = raw(&pair.membership.siblings[14]);
+    sibs[15] = [pair.membership.siblings[14][0].0, pair.membership.siblings[14][1].0, pair.membership.siblings[14][2].0, pair.membership.siblings[14][3].0, pair.membership.siblings[14][4].0, pair.membership.siblings[14][5].0, pair.membership.siblings[14][6].0, pair.membership.siblings[14][7].0];
     bits[16] = ((pair.membership.index >> 15) & 1) as u32;
-    sibs[16] = raw(&pair.membership.siblings[15]);
+    sibs[16] = [pair.membership.siblings[15][0].0, pair.membership.siblings[15][1].0, pair.membership.siblings[15][2].0, pair.membership.siblings[15][3].0, pair.membership.siblings[15][4].0, pair.membership.siblings[15][5].0, pair.membership.siblings[15][6].0, pair.membership.siblings[15][7].0];
     bits[17] = ((pair.membership.index >> 16) & 1) as u32;
-    sibs[17] = raw(&pair.membership.siblings[16]);
+    sibs[17] = [pair.membership.siblings[16][0].0, pair.membership.siblings[16][1].0, pair.membership.siblings[16][2].0, pair.membership.siblings[16][3].0, pair.membership.siblings[16][4].0, pair.membership.siblings[16][5].0, pair.membership.siblings[16][6].0, pair.membership.siblings[16][7].0];
     bits[18] = ((pair.membership.index >> 17) & 1) as u32;
-    sibs[18] = raw(&pair.membership.siblings[17]);
+    sibs[18] = [pair.membership.siblings[17][0].0, pair.membership.siblings[17][1].0, pair.membership.siblings[17][2].0, pair.membership.siblings[17][3].0, pair.membership.siblings[17][4].0, pair.membership.siblings[17][5].0, pair.membership.siblings[17][6].0, pair.membership.siblings[17][7].0];
     bits[19] = ((pair.membership.index >> 18) & 1) as u32;
-    sibs[19] = raw(&pair.membership.siblings[18]);
+    sibs[19] = [pair.membership.siblings[18][0].0, pair.membership.siblings[18][1].0, pair.membership.siblings[18][2].0, pair.membership.siblings[18][3].0, pair.membership.siblings[18][4].0, pair.membership.siblings[18][5].0, pair.membership.siblings[18][6].0, pair.membership.siblings[18][7].0];
     bits[20] = ((pair.membership.index >> 19) & 1) as u32;
-    sibs[20] = raw(&pair.membership.siblings[19]);
+    sibs[20] = [pair.membership.siblings[19][0].0, pair.membership.siblings[19][1].0, pair.membership.siblings[19][2].0, pair.membership.siblings[19][3].0, pair.membership.siblings[19][4].0, pair.membership.siblings[19][5].0, pair.membership.siblings[19][6].0, pair.membership.siblings[19][7].0];
     bits[21] = u32::from(input.super_root_directions[0]);
-    sibs[21] = raw(&input.super_root_siblings[0]);
+    sibs[21] = [input.super_root_siblings[0][0].0, input.super_root_siblings[0][1].0, input.super_root_siblings[0][2].0, input.super_root_siblings[0][3].0, input.super_root_siblings[0][4].0, input.super_root_siblings[0][5].0, input.super_root_siblings[0][6].0, input.super_root_siblings[0][7].0];
     bits[22] = u32::from(input.super_root_directions[1]);
-    sibs[22] = raw(&input.super_root_siblings[1]);
+    sibs[22] = [input.super_root_siblings[1][0].0, input.super_root_siblings[1][1].0, input.super_root_siblings[1][2].0, input.super_root_siblings[1][3].0, input.super_root_siblings[1][4].0, input.super_root_siblings[1][5].0, input.super_root_siblings[1][6].0, input.super_root_siblings[1][7].0];
     bits[23] = u32::from(input.super_root_directions[2]);
-    sibs[23] = raw(&input.super_root_siblings[2]);
+    sibs[23] = [input.super_root_siblings[2][0].0, input.super_root_siblings[2][1].0, input.super_root_siblings[2][2].0, input.super_root_siblings[2][3].0, input.super_root_siblings[2][4].0, input.super_root_siblings[2][5].0, input.super_root_siblings[2][6].0, input.super_root_siblings[2][7].0];
     let empty = pair_empty_roots();
     let (recipient_key, recipient_note_salt, transfer) = match rec {
         Some(r) => (r.owner_key, r.salt, true),
         None => ([M31(0); 8], [M31(0); 8], false),
     };
-    let recipient_owner = raw(&recipient_key);
-    let recipient_salt = raw(&recipient_note_salt);
+    let recipient_owner = [recipient_key[0].0, recipient_key[1].0, recipient_key[2].0, recipient_key[3].0, recipient_key[4].0, recipient_key[5].0, recipient_key[6].0, recipient_key[7].0];
+    let recipient_salt = [recipient_note_salt[0].0, recipient_note_salt[1].0, recipient_note_salt[2].0, recipient_note_salt[3].0, recipient_note_salt[4].0, recipient_note_salt[5].0, recipient_note_salt[6].0, recipient_note_salt[7].0];
     let w = RW {
         input_value: pair.value,
         output_value: out,
         change_value: chg.value,
-        sk: raw(&pair.nullifier_key),
-        salt: raw(&pair.salt),
+        sk: [pair.nullifier_key[0].0, pair.nullifier_key[1].0, pair.nullifier_key[2].0, pair.nullifier_key[3].0, pair.nullifier_key[4].0, pair.nullifier_key[5].0, pair.nullifier_key[6].0, pair.nullifier_key[7].0],
+        salt: [pair.salt[0].0, pair.salt[1].0, pair.salt[2].0, pair.salt[3].0, pair.salt[4].0, pair.salt[5].0, pair.salt[6].0, pair.salt[7].0],
         bits,
         sibs,
-        pair_first: raw(&pair.pair_leaf.first_commitment),
+        pair_first: [pair.pair_leaf.first_commitment[0].0, pair.pair_leaf.first_commitment[1].0, pair.pair_leaf.first_commitment[2].0, pair.pair_leaf.first_commitment[3].0, pair.pair_leaf.first_commitment[4].0, pair.pair_leaf.first_commitment[5].0, pair.pair_leaf.first_commitment[6].0, pair.pair_leaf.first_commitment[7].0],
         pair_occupied: pair.pair_leaf.second_occupied.0,
-        pair_second: raw(&pair.pair_leaf.second_commitment),
+        pair_second: [pair.pair_leaf.second_commitment[0].0, pair.pair_leaf.second_commitment[1].0, pair.pair_leaf.second_commitment[2].0, pair.pair_leaf.second_commitment[3].0, pair.pair_leaf.second_commitment[4].0, pair.pair_leaf.second_commitment[5].0, pair.pair_leaf.second_commitment[6].0, pair.pair_leaf.second_commitment[7].0],
         pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
         recipient_owner,
         recipient_salt,
-        change_owner: raw(&chg.owner_key),
-        change_salt: raw(&chg.salt),
+        change_owner: [chg.owner_key[0].0, chg.owner_key[1].0, chg.owner_key[2].0, chg.owner_key[3].0, chg.owner_key[4].0, chg.owner_key[5].0, chg.owner_key[6].0, chg.owner_key[7].0],
+        change_salt: [chg.salt[0].0, chg.salt[1].0, chg.salt[2].0, chg.salt[3].0, chg.salt[4].0, chg.salt[5].0, chg.salt[6].0, chg.salt[7].0],
     };
     let p = RP {
         transfer,
         asset: asset.0,
         next_pair_index: snapshot.next_pair_index,
         frontier: [
-            raw(&snapshot.frontier[0]),
-            raw(&snapshot.frontier[1]),
-            raw(&snapshot.frontier[2]),
-            raw(&snapshot.frontier[3]),
-            raw(&snapshot.frontier[4]),
-            raw(&snapshot.frontier[5]),
-            raw(&snapshot.frontier[6]),
-            raw(&snapshot.frontier[7]),
-            raw(&snapshot.frontier[8]),
-            raw(&snapshot.frontier[9]),
-            raw(&snapshot.frontier[10]),
-            raw(&snapshot.frontier[11]),
-            raw(&snapshot.frontier[12]),
-            raw(&snapshot.frontier[13]),
-            raw(&snapshot.frontier[14]),
-            raw(&snapshot.frontier[15]),
-            raw(&snapshot.frontier[16]),
-            raw(&snapshot.frontier[17]),
-            raw(&snapshot.frontier[18]),
-            raw(&snapshot.frontier[19]),
+            [snapshot.frontier[0][0].0, snapshot.frontier[0][1].0, snapshot.frontier[0][2].0, snapshot.frontier[0][3].0, snapshot.frontier[0][4].0, snapshot.frontier[0][5].0, snapshot.frontier[0][6].0, snapshot.frontier[0][7].0],
+            [snapshot.frontier[1][0].0, snapshot.frontier[1][1].0, snapshot.frontier[1][2].0, snapshot.frontier[1][3].0, snapshot.frontier[1][4].0, snapshot.frontier[1][5].0, snapshot.frontier[1][6].0, snapshot.frontier[1][7].0],
+            [snapshot.frontier[2][0].0, snapshot.frontier[2][1].0, snapshot.frontier[2][2].0, snapshot.frontier[2][3].0, snapshot.frontier[2][4].0, snapshot.frontier[2][5].0, snapshot.frontier[2][6].0, snapshot.frontier[2][7].0],
+            [snapshot.frontier[3][0].0, snapshot.frontier[3][1].0, snapshot.frontier[3][2].0, snapshot.frontier[3][3].0, snapshot.frontier[3][4].0, snapshot.frontier[3][5].0, snapshot.frontier[3][6].0, snapshot.frontier[3][7].0],
+            [snapshot.frontier[4][0].0, snapshot.frontier[4][1].0, snapshot.frontier[4][2].0, snapshot.frontier[4][3].0, snapshot.frontier[4][4].0, snapshot.frontier[4][5].0, snapshot.frontier[4][6].0, snapshot.frontier[4][7].0],
+            [snapshot.frontier[5][0].0, snapshot.frontier[5][1].0, snapshot.frontier[5][2].0, snapshot.frontier[5][3].0, snapshot.frontier[5][4].0, snapshot.frontier[5][5].0, snapshot.frontier[5][6].0, snapshot.frontier[5][7].0],
+            [snapshot.frontier[6][0].0, snapshot.frontier[6][1].0, snapshot.frontier[6][2].0, snapshot.frontier[6][3].0, snapshot.frontier[6][4].0, snapshot.frontier[6][5].0, snapshot.frontier[6][6].0, snapshot.frontier[6][7].0],
+            [snapshot.frontier[7][0].0, snapshot.frontier[7][1].0, snapshot.frontier[7][2].0, snapshot.frontier[7][3].0, snapshot.frontier[7][4].0, snapshot.frontier[7][5].0, snapshot.frontier[7][6].0, snapshot.frontier[7][7].0],
+            [snapshot.frontier[8][0].0, snapshot.frontier[8][1].0, snapshot.frontier[8][2].0, snapshot.frontier[8][3].0, snapshot.frontier[8][4].0, snapshot.frontier[8][5].0, snapshot.frontier[8][6].0, snapshot.frontier[8][7].0],
+            [snapshot.frontier[9][0].0, snapshot.frontier[9][1].0, snapshot.frontier[9][2].0, snapshot.frontier[9][3].0, snapshot.frontier[9][4].0, snapshot.frontier[9][5].0, snapshot.frontier[9][6].0, snapshot.frontier[9][7].0],
+            [snapshot.frontier[10][0].0, snapshot.frontier[10][1].0, snapshot.frontier[10][2].0, snapshot.frontier[10][3].0, snapshot.frontier[10][4].0, snapshot.frontier[10][5].0, snapshot.frontier[10][6].0, snapshot.frontier[10][7].0],
+            [snapshot.frontier[11][0].0, snapshot.frontier[11][1].0, snapshot.frontier[11][2].0, snapshot.frontier[11][3].0, snapshot.frontier[11][4].0, snapshot.frontier[11][5].0, snapshot.frontier[11][6].0, snapshot.frontier[11][7].0],
+            [snapshot.frontier[12][0].0, snapshot.frontier[12][1].0, snapshot.frontier[12][2].0, snapshot.frontier[12][3].0, snapshot.frontier[12][4].0, snapshot.frontier[12][5].0, snapshot.frontier[12][6].0, snapshot.frontier[12][7].0],
+            [snapshot.frontier[13][0].0, snapshot.frontier[13][1].0, snapshot.frontier[13][2].0, snapshot.frontier[13][3].0, snapshot.frontier[13][4].0, snapshot.frontier[13][5].0, snapshot.frontier[13][6].0, snapshot.frontier[13][7].0],
+            [snapshot.frontier[14][0].0, snapshot.frontier[14][1].0, snapshot.frontier[14][2].0, snapshot.frontier[14][3].0, snapshot.frontier[14][4].0, snapshot.frontier[14][5].0, snapshot.frontier[14][6].0, snapshot.frontier[14][7].0],
+            [snapshot.frontier[15][0].0, snapshot.frontier[15][1].0, snapshot.frontier[15][2].0, snapshot.frontier[15][3].0, snapshot.frontier[15][4].0, snapshot.frontier[15][5].0, snapshot.frontier[15][6].0, snapshot.frontier[15][7].0],
+            [snapshot.frontier[16][0].0, snapshot.frontier[16][1].0, snapshot.frontier[16][2].0, snapshot.frontier[16][3].0, snapshot.frontier[16][4].0, snapshot.frontier[16][5].0, snapshot.frontier[16][6].0, snapshot.frontier[16][7].0],
+            [snapshot.frontier[17][0].0, snapshot.frontier[17][1].0, snapshot.frontier[17][2].0, snapshot.frontier[17][3].0, snapshot.frontier[17][4].0, snapshot.frontier[17][5].0, snapshot.frontier[17][6].0, snapshot.frontier[17][7].0],
+            [snapshot.frontier[18][0].0, snapshot.frontier[18][1].0, snapshot.frontier[18][2].0, snapshot.frontier[18][3].0, snapshot.frontier[18][4].0, snapshot.frontier[18][5].0, snapshot.frontier[18][6].0, snapshot.frontier[18][7].0],
+            [snapshot.frontier[19][0].0, snapshot.frontier[19][1].0, snapshot.frontier[19][2].0, snapshot.frontier[19][3].0, snapshot.frontier[19][4].0, snapshot.frontier[19][5].0, snapshot.frontier[19][6].0, snapshot.frontier[19][7].0],
         ],
         empty: [
-            raw(&empty[0]),
-            raw(&empty[1]),
-            raw(&empty[2]),
-            raw(&empty[3]),
-            raw(&empty[4]),
-            raw(&empty[5]),
-            raw(&empty[6]),
-            raw(&empty[7]),
-            raw(&empty[8]),
-            raw(&empty[9]),
-            raw(&empty[10]),
-            raw(&empty[11]),
-            raw(&empty[12]),
-            raw(&empty[13]),
-            raw(&empty[14]),
-            raw(&empty[15]),
-            raw(&empty[16]),
-            raw(&empty[17]),
-            raw(&empty[18]),
-            raw(&empty[19]),
+            [empty[0][0].0, empty[0][1].0, empty[0][2].0, empty[0][3].0, empty[0][4].0, empty[0][5].0, empty[0][6].0, empty[0][7].0],
+            [empty[1][0].0, empty[1][1].0, empty[1][2].0, empty[1][3].0, empty[1][4].0, empty[1][5].0, empty[1][6].0, empty[1][7].0],
+            [empty[2][0].0, empty[2][1].0, empty[2][2].0, empty[2][3].0, empty[2][4].0, empty[2][5].0, empty[2][6].0, empty[2][7].0],
+            [empty[3][0].0, empty[3][1].0, empty[3][2].0, empty[3][3].0, empty[3][4].0, empty[3][5].0, empty[3][6].0, empty[3][7].0],
+            [empty[4][0].0, empty[4][1].0, empty[4][2].0, empty[4][3].0, empty[4][4].0, empty[4][5].0, empty[4][6].0, empty[4][7].0],
+            [empty[5][0].0, empty[5][1].0, empty[5][2].0, empty[5][3].0, empty[5][4].0, empty[5][5].0, empty[5][6].0, empty[5][7].0],
+            [empty[6][0].0, empty[6][1].0, empty[6][2].0, empty[6][3].0, empty[6][4].0, empty[6][5].0, empty[6][6].0, empty[6][7].0],
+            [empty[7][0].0, empty[7][1].0, empty[7][2].0, empty[7][3].0, empty[7][4].0, empty[7][5].0, empty[7][6].0, empty[7][7].0],
+            [empty[8][0].0, empty[8][1].0, empty[8][2].0, empty[8][3].0, empty[8][4].0, empty[8][5].0, empty[8][6].0, empty[8][7].0],
+            [empty[9][0].0, empty[9][1].0, empty[9][2].0, empty[9][3].0, empty[9][4].0, empty[9][5].0, empty[9][6].0, empty[9][7].0],
+            [empty[10][0].0, empty[10][1].0, empty[10][2].0, empty[10][3].0, empty[10][4].0, empty[10][5].0, empty[10][6].0, empty[10][7].0],
+            [empty[11][0].0, empty[11][1].0, empty[11][2].0, empty[11][3].0, empty[11][4].0, empty[11][5].0, empty[11][6].0, empty[11][7].0],
+            [empty[12][0].0, empty[12][1].0, empty[12][2].0, empty[12][3].0, empty[12][4].0, empty[12][5].0, empty[12][6].0, empty[12][7].0],
+            [empty[13][0].0, empty[13][1].0, empty[13][2].0, empty[13][3].0, empty[13][4].0, empty[13][5].0, empty[13][6].0, empty[13][7].0],
+            [empty[14][0].0, empty[14][1].0, empty[14][2].0, empty[14][3].0, empty[14][4].0, empty[14][5].0, empty[14][6].0, empty[14][7].0],
+            [empty[15][0].0, empty[15][1].0, empty[15][2].0, empty[15][3].0, empty[15][4].0, empty[15][5].0, empty[15][6].0, empty[15][7].0],
+            [empty[16][0].0, empty[16][1].0, empty[16][2].0, empty[16][3].0, empty[16][4].0, empty[16][5].0, empty[16][6].0, empty[16][7].0],
+            [empty[17][0].0, empty[17][1].0, empty[17][2].0, empty[17][3].0, empty[17][4].0, empty[17][5].0, empty[17][6].0, empty[17][7].0],
+            [empty[18][0].0, empty[18][1].0, empty[18][2].0, empty[18][3].0, empty[18][4].0, empty[18][5].0, empty[18][6].0, empty[18][7].0],
+            [empty[19][0].0, empty[19][1].0, empty[19][2].0, empty[19][3].0, empty[19][4].0, empty[19][5].0, empty[19][6].0, empty[19][7].0],
         ],
     };
     (w, p)
```

No diagnostic for repair 9 started: reservation refused. This independent
concretization removes records' dependency on the opaque raw helper without
changing raw or any other function. raw(d) is exactly
core::array::from_fn(|i| d[i].0) for a Digest=[M31;8]; each replacement is
the same eight field reads, indices 0..7 ascending. Every argument is an
immutable local or fixed in-bounds array projection, without side effects.
Repeated evaluation of the argument projection cannot panic or change values.
All 72 returned arrays are identical, including zero recipient digests. No
new allocation, I/O, panic/abort, signature or type change. M31 Copy derive
is field.rs:22; witness Copy derives remain as recorded above.

11. D277, own the optional note at entry, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 63b88b2ca0..06df9cddcb 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -226,6 +226,7 @@ include!("../../../../docs/research/v8-r0-zk-20261009/refine/diffharness/tests/g
 
 fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
            chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
+    let rec = match rec { Some(r) => Some(*r), None => None };
     let input = *input;
     let chg = *chg;
     let snapshot = *snapshot;
```

Repair 10 exits 2 (196.723s, 6,273,101,824 bytes peak, zero swap) at
records:286:20–31 / InterpBorrowsCore.ml:629, copying r.salt from the
borrowed optional note. Entry match now maps None to None and Some(&r)
to Some(r), using its Copy derive payment_relation.rs:88. All later
recipient reads and transfer discrimination operate on an identical owned
optional value. The signature, types, returned values, panics/aborts,
allocation and I/O behavior remain identical; no other function changes.

12. D277, sink recipient reads to the final return branch, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 06df9cddcb..eb2c7376e0 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -226,7 +226,6 @@ include!("../../../../docs/research/v8-r0-zk-20261009/refine/diffharness/tests/g
 
 fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
            chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
-    let rec = match rec { Some(r) => Some(*r), None => None };
     let input = *input;
     let chg = *chg;
     let snapshot = *snapshot;
@@ -283,13 +282,7 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     bits[23] = u32::from(input.super_root_directions[2]);
     sibs[23] = [input.super_root_siblings[2][0].0, input.super_root_siblings[2][1].0, input.super_root_siblings[2][2].0, input.super_root_siblings[2][3].0, input.super_root_siblings[2][4].0, input.super_root_siblings[2][5].0, input.super_root_siblings[2][6].0, input.super_root_siblings[2][7].0];
     let empty = pair_empty_roots();
-    let (recipient_key, recipient_note_salt, transfer) = match rec {
-        Some(r) => (r.owner_key, r.salt, true),
-        None => ([M31(0); 8], [M31(0); 8], false),
-    };
-    let recipient_owner = [recipient_key[0].0, recipient_key[1].0, recipient_key[2].0, recipient_key[3].0, recipient_key[4].0, recipient_key[5].0, recipient_key[6].0, recipient_key[7].0];
-    let recipient_salt = [recipient_note_salt[0].0, recipient_note_salt[1].0, recipient_note_salt[2].0, recipient_note_salt[3].0, recipient_note_salt[4].0, recipient_note_salt[5].0, recipient_note_salt[6].0, recipient_note_salt[7].0];
-    let w = RW {
+    let mut w = RW {
         input_value: pair.value,
         output_value: out,
         change_value: chg.value,
@@ -301,13 +294,13 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
         pair_occupied: pair.pair_leaf.second_occupied.0,
         pair_second: [pair.pair_leaf.second_commitment[0].0, pair.pair_leaf.second_commitment[1].0, pair.pair_leaf.second_commitment[2].0, pair.pair_leaf.second_commitment[3].0, pair.pair_leaf.second_commitment[4].0, pair.pair_leaf.second_commitment[5].0, pair.pair_leaf.second_commitment[6].0, pair.pair_leaf.second_commitment[7].0],
         pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
-        recipient_owner,
-        recipient_salt,
+        recipient_owner: ZERO8,
+        recipient_salt: ZERO8,
         change_owner: [chg.owner_key[0].0, chg.owner_key[1].0, chg.owner_key[2].0, chg.owner_key[3].0, chg.owner_key[4].0, chg.owner_key[5].0, chg.owner_key[6].0, chg.owner_key[7].0],
         change_salt: [chg.salt[0].0, chg.salt[1].0, chg.salt[2].0, chg.salt[3].0, chg.salt[4].0, chg.salt[5].0, chg.salt[6].0, chg.salt[7].0],
     };
-    let p = RP {
-        transfer,
+    let mut p = RP {
+        transfer: false,
         asset: asset.0,
         next_pair_index: snapshot.next_pair_index,
         frontier: [
@@ -355,7 +348,16 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
             [empty[19][0].0, empty[19][1].0, empty[19][2].0, empty[19][3].0, empty[19][4].0, empty[19][5].0, empty[19][6].0, empty[19][7].0],
         ],
     };
-    (w, p)
+    match rec {
+        Some(r) => {
+            let r = *r;
+            w.recipient_owner = [r.owner_key[0].0, r.owner_key[1].0, r.owner_key[2].0, r.owner_key[3].0, r.owner_key[4].0, r.owner_key[5].0, r.owner_key[6].0, r.owner_key[7].0];
+            w.recipient_salt = [r.salt[0].0, r.salt[1].0, r.salt[2].0, r.salt[3].0, r.salt[4].0, r.salt[5].0, r.salt[6].0, r.salt[7].0];
+            p.transfer = true;
+            (w, p)
+        },
+        None => (w, p),
+    }
 }
 
 // ---------- interface for the forest compiler ----------
```

Repair 11 fails at the entry option join (records:229 / InterpAbs.ml:1955).
The shared record body now builds zero recipient words and transfer=false.
None returns those exact original values. Some(r) copies the note
(payment_relation.rs:88), writes exactly its eight owner words and eight
salt words into w, sets p.transfer=true, and returns. All other RW/RP
fields and empty-root call are unchanged. Delayed field reads are pure,
in bounds, panic/abort-free, with no allocation or I/O. No code follows
the match, removing the need to carry its optional borrow into later work.
No signature/type/other-function changes.

13. D277, destructure digest arrays rather than calling shared index,
verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index eb2c7376e0..4a23003366 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -234,125 +234,125 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let mut bits = [0u32; 24];
     let mut sibs = [[0u32; 8]; 24];
     bits[0] = u32::from(pair.selected_second);
-    sibs[0] = [other[0].0, other[1].0, other[2].0, other[3].0, other[4].0, other[5].0, other[6].0, other[7].0];
+    sibs[0] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = other; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[1] = ((pair.membership.index >> 0) & 1) as u32;
-    sibs[1] = [pair.membership.siblings[0][0].0, pair.membership.siblings[0][1].0, pair.membership.siblings[0][2].0, pair.membership.siblings[0][3].0, pair.membership.siblings[0][4].0, pair.membership.siblings[0][5].0, pair.membership.siblings[0][6].0, pair.membership.siblings[0][7].0];
+    sibs[1] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[0]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[2] = ((pair.membership.index >> 1) & 1) as u32;
-    sibs[2] = [pair.membership.siblings[1][0].0, pair.membership.siblings[1][1].0, pair.membership.siblings[1][2].0, pair.membership.siblings[1][3].0, pair.membership.siblings[1][4].0, pair.membership.siblings[1][5].0, pair.membership.siblings[1][6].0, pair.membership.siblings[1][7].0];
+    sibs[2] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[1]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[3] = ((pair.membership.index >> 2) & 1) as u32;
-    sibs[3] = [pair.membership.siblings[2][0].0, pair.membership.siblings[2][1].0, pair.membership.siblings[2][2].0, pair.membership.siblings[2][3].0, pair.membership.siblings[2][4].0, pair.membership.siblings[2][5].0, pair.membership.siblings[2][6].0, pair.membership.siblings[2][7].0];
+    sibs[3] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[2]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[4] = ((pair.membership.index >> 3) & 1) as u32;
-    sibs[4] = [pair.membership.siblings[3][0].0, pair.membership.siblings[3][1].0, pair.membership.siblings[3][2].0, pair.membership.siblings[3][3].0, pair.membership.siblings[3][4].0, pair.membership.siblings[3][5].0, pair.membership.siblings[3][6].0, pair.membership.siblings[3][7].0];
+    sibs[4] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[3]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[5] = ((pair.membership.index >> 4) & 1) as u32;
-    sibs[5] = [pair.membership.siblings[4][0].0, pair.membership.siblings[4][1].0, pair.membership.siblings[4][2].0, pair.membership.siblings[4][3].0, pair.membership.siblings[4][4].0, pair.membership.siblings[4][5].0, pair.membership.siblings[4][6].0, pair.membership.siblings[4][7].0];
+    sibs[5] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[4]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[6] = ((pair.membership.index >> 5) & 1) as u32;
-    sibs[6] = [pair.membership.siblings[5][0].0, pair.membership.siblings[5][1].0, pair.membership.siblings[5][2].0, pair.membership.siblings[5][3].0, pair.membership.siblings[5][4].0, pair.membership.siblings[5][5].0, pair.membership.siblings[5][6].0, pair.membership.siblings[5][7].0];
+    sibs[6] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[5]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[7] = ((pair.membership.index >> 6) & 1) as u32;
-    sibs[7] = [pair.membership.siblings[6][0].0, pair.membership.siblings[6][1].0, pair.membership.siblings[6][2].0, pair.membership.siblings[6][3].0, pair.membership.siblings[6][4].0, pair.membership.siblings[6][5].0, pair.membership.siblings[6][6].0, pair.membership.siblings[6][7].0];
+    sibs[7] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[6]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[8] = ((pair.membership.index >> 7) & 1) as u32;
-    sibs[8] = [pair.membership.siblings[7][0].0, pair.membership.siblings[7][1].0, pair.membership.siblings[7][2].0, pair.membership.siblings[7][3].0, pair.membership.siblings[7][4].0, pair.membership.siblings[7][5].0, pair.membership.siblings[7][6].0, pair.membership.siblings[7][7].0];
+    sibs[8] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[7]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[9] = ((pair.membership.index >> 8) & 1) as u32;
-    sibs[9] = [pair.membership.siblings[8][0].0, pair.membership.siblings[8][1].0, pair.membership.siblings[8][2].0, pair.membership.siblings[8][3].0, pair.membership.siblings[8][4].0, pair.membership.siblings[8][5].0, pair.membership.siblings[8][6].0, pair.membership.siblings[8][7].0];
+    sibs[9] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[8]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[10] = ((pair.membership.index >> 9) & 1) as u32;
-    sibs[10] = [pair.membership.siblings[9][0].0, pair.membership.siblings[9][1].0, pair.membership.siblings[9][2].0, pair.membership.siblings[9][3].0, pair.membership.siblings[9][4].0, pair.membership.siblings[9][5].0, pair.membership.siblings[9][6].0, pair.membership.siblings[9][7].0];
+    sibs[10] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[9]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[11] = ((pair.membership.index >> 10) & 1) as u32;
-    sibs[11] = [pair.membership.siblings[10][0].0, pair.membership.siblings[10][1].0, pair.membership.siblings[10][2].0, pair.membership.siblings[10][3].0, pair.membership.siblings[10][4].0, pair.membership.siblings[10][5].0, pair.membership.siblings[10][6].0, pair.membership.siblings[10][7].0];
+    sibs[11] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[10]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[12] = ((pair.membership.index >> 11) & 1) as u32;
-    sibs[12] = [pair.membership.siblings[11][0].0, pair.membership.siblings[11][1].0, pair.membership.siblings[11][2].0, pair.membership.siblings[11][3].0, pair.membership.siblings[11][4].0, pair.membership.siblings[11][5].0, pair.membership.siblings[11][6].0, pair.membership.siblings[11][7].0];
+    sibs[12] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[11]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[13] = ((pair.membership.index >> 12) & 1) as u32;
-    sibs[13] = [pair.membership.siblings[12][0].0, pair.membership.siblings[12][1].0, pair.membership.siblings[12][2].0, pair.membership.siblings[12][3].0, pair.membership.siblings[12][4].0, pair.membership.siblings[12][5].0, pair.membership.siblings[12][6].0, pair.membership.siblings[12][7].0];
+    sibs[13] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[12]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[14] = ((pair.membership.index >> 13) & 1) as u32;
-    sibs[14] = [pair.membership.siblings[13][0].0, pair.membership.siblings[13][1].0, pair.membership.siblings[13][2].0, pair.membership.siblings[13][3].0, pair.membership.siblings[13][4].0, pair.membership.siblings[13][5].0, pair.membership.siblings[13][6].0, pair.membership.siblings[13][7].0];
+    sibs[14] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[13]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[15] = ((pair.membership.index >> 14) & 1) as u32;
-    sibs[15] = [pair.membership.siblings[14][0].0, pair.membership.siblings[14][1].0, pair.membership.siblings[14][2].0, pair.membership.siblings[14][3].0, pair.membership.siblings[14][4].0, pair.membership.siblings[14][5].0, pair.membership.siblings[14][6].0, pair.membership.siblings[14][7].0];
+    sibs[15] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[14]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[16] = ((pair.membership.index >> 15) & 1) as u32;
-    sibs[16] = [pair.membership.siblings[15][0].0, pair.membership.siblings[15][1].0, pair.membership.siblings[15][2].0, pair.membership.siblings[15][3].0, pair.membership.siblings[15][4].0, pair.membership.siblings[15][5].0, pair.membership.siblings[15][6].0, pair.membership.siblings[15][7].0];
+    sibs[16] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[15]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[17] = ((pair.membership.index >> 16) & 1) as u32;
-    sibs[17] = [pair.membership.siblings[16][0].0, pair.membership.siblings[16][1].0, pair.membership.siblings[16][2].0, pair.membership.siblings[16][3].0, pair.membership.siblings[16][4].0, pair.membership.siblings[16][5].0, pair.membership.siblings[16][6].0, pair.membership.siblings[16][7].0];
+    sibs[17] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[16]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[18] = ((pair.membership.index >> 17) & 1) as u32;
-    sibs[18] = [pair.membership.siblings[17][0].0, pair.membership.siblings[17][1].0, pair.membership.siblings[17][2].0, pair.membership.siblings[17][3].0, pair.membership.siblings[17][4].0, pair.membership.siblings[17][5].0, pair.membership.siblings[17][6].0, pair.membership.siblings[17][7].0];
+    sibs[18] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[17]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[19] = ((pair.membership.index >> 18) & 1) as u32;
-    sibs[19] = [pair.membership.siblings[18][0].0, pair.membership.siblings[18][1].0, pair.membership.siblings[18][2].0, pair.membership.siblings[18][3].0, pair.membership.siblings[18][4].0, pair.membership.siblings[18][5].0, pair.membership.siblings[18][6].0, pair.membership.siblings[18][7].0];
+    sibs[19] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[18]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[20] = ((pair.membership.index >> 19) & 1) as u32;
-    sibs[20] = [pair.membership.siblings[19][0].0, pair.membership.siblings[19][1].0, pair.membership.siblings[19][2].0, pair.membership.siblings[19][3].0, pair.membership.siblings[19][4].0, pair.membership.siblings[19][5].0, pair.membership.siblings[19][6].0, pair.membership.siblings[19][7].0];
+    sibs[20] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[19]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[21] = u32::from(input.super_root_directions[0]);
-    sibs[21] = [input.super_root_siblings[0][0].0, input.super_root_siblings[0][1].0, input.super_root_siblings[0][2].0, input.super_root_siblings[0][3].0, input.super_root_siblings[0][4].0, input.super_root_siblings[0][5].0, input.super_root_siblings[0][6].0, input.super_root_siblings[0][7].0];
+    sibs[21] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = input.super_root_siblings[0]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[22] = u32::from(input.super_root_directions[1]);
-    sibs[22] = [input.super_root_siblings[1][0].0, input.super_root_siblings[1][1].0, input.super_root_siblings[1][2].0, input.super_root_siblings[1][3].0, input.super_root_siblings[1][4].0, input.super_root_siblings[1][5].0, input.super_root_siblings[1][6].0, input.super_root_siblings[1][7].0];
+    sibs[22] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = input.super_root_siblings[1]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     bits[23] = u32::from(input.super_root_directions[2]);
-    sibs[23] = [input.super_root_siblings[2][0].0, input.super_root_siblings[2][1].0, input.super_root_siblings[2][2].0, input.super_root_siblings[2][3].0, input.super_root_siblings[2][4].0, input.super_root_siblings[2][5].0, input.super_root_siblings[2][6].0, input.super_root_siblings[2][7].0];
+    sibs[23] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = input.super_root_siblings[2]; [w0, w1, w2, w3, w4, w5, w6, w7] };
     let empty = pair_empty_roots();
     let mut w = RW {
         input_value: pair.value,
         output_value: out,
         change_value: chg.value,
-        sk: [pair.nullifier_key[0].0, pair.nullifier_key[1].0, pair.nullifier_key[2].0, pair.nullifier_key[3].0, pair.nullifier_key[4].0, pair.nullifier_key[5].0, pair.nullifier_key[6].0, pair.nullifier_key[7].0],
-        salt: [pair.salt[0].0, pair.salt[1].0, pair.salt[2].0, pair.salt[3].0, pair.salt[4].0, pair.salt[5].0, pair.salt[6].0, pair.salt[7].0],
+        sk: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.nullifier_key; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        salt: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.salt; [w0, w1, w2, w3, w4, w5, w6, w7] },
         bits,
         sibs,
-        pair_first: [pair.pair_leaf.first_commitment[0].0, pair.pair_leaf.first_commitment[1].0, pair.pair_leaf.first_commitment[2].0, pair.pair_leaf.first_commitment[3].0, pair.pair_leaf.first_commitment[4].0, pair.pair_leaf.first_commitment[5].0, pair.pair_leaf.first_commitment[6].0, pair.pair_leaf.first_commitment[7].0],
+        pair_first: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.pair_leaf.first_commitment; [w0, w1, w2, w3, w4, w5, w6, w7] },
         pair_occupied: pair.pair_leaf.second_occupied.0,
-        pair_second: [pair.pair_leaf.second_commitment[0].0, pair.pair_leaf.second_commitment[1].0, pair.pair_leaf.second_commitment[2].0, pair.pair_leaf.second_commitment[3].0, pair.pair_leaf.second_commitment[4].0, pair.pair_leaf.second_commitment[5].0, pair.pair_leaf.second_commitment[6].0, pair.pair_leaf.second_commitment[7].0],
+        pair_second: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.pair_leaf.second_commitment; [w0, w1, w2, w3, w4, w5, w6, w7] },
         pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
         recipient_owner: ZERO8,
         recipient_salt: ZERO8,
-        change_owner: [chg.owner_key[0].0, chg.owner_key[1].0, chg.owner_key[2].0, chg.owner_key[3].0, chg.owner_key[4].0, chg.owner_key[5].0, chg.owner_key[6].0, chg.owner_key[7].0],
-        change_salt: [chg.salt[0].0, chg.salt[1].0, chg.salt[2].0, chg.salt[3].0, chg.salt[4].0, chg.salt[5].0, chg.salt[6].0, chg.salt[7].0],
+        change_owner: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = chg.owner_key; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        change_salt: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = chg.salt; [w0, w1, w2, w3, w4, w5, w6, w7] },
     };
     let mut p = RP {
         transfer: false,
         asset: asset.0,
         next_pair_index: snapshot.next_pair_index,
         frontier: [
-            [snapshot.frontier[0][0].0, snapshot.frontier[0][1].0, snapshot.frontier[0][2].0, snapshot.frontier[0][3].0, snapshot.frontier[0][4].0, snapshot.frontier[0][5].0, snapshot.frontier[0][6].0, snapshot.frontier[0][7].0],
-            [snapshot.frontier[1][0].0, snapshot.frontier[1][1].0, snapshot.frontier[1][2].0, snapshot.frontier[1][3].0, snapshot.frontier[1][4].0, snapshot.frontier[1][5].0, snapshot.frontier[1][6].0, snapshot.frontier[1][7].0],
-            [snapshot.frontier[2][0].0, snapshot.frontier[2][1].0, snapshot.frontier[2][2].0, snapshot.frontier[2][3].0, snapshot.frontier[2][4].0, snapshot.frontier[2][5].0, snapshot.frontier[2][6].0, snapshot.frontier[2][7].0],
-            [snapshot.frontier[3][0].0, snapshot.frontier[3][1].0, snapshot.frontier[3][2].0, snapshot.frontier[3][3].0, snapshot.frontier[3][4].0, snapshot.frontier[3][5].0, snapshot.frontier[3][6].0, snapshot.frontier[3][7].0],
-            [snapshot.frontier[4][0].0, snapshot.frontier[4][1].0, snapshot.frontier[4][2].0, snapshot.frontier[4][3].0, snapshot.frontier[4][4].0, snapshot.frontier[4][5].0, snapshot.frontier[4][6].0, snapshot.frontier[4][7].0],
-            [snapshot.frontier[5][0].0, snapshot.frontier[5][1].0, snapshot.frontier[5][2].0, snapshot.frontier[5][3].0, snapshot.frontier[5][4].0, snapshot.frontier[5][5].0, snapshot.frontier[5][6].0, snapshot.frontier[5][7].0],
-            [snapshot.frontier[6][0].0, snapshot.frontier[6][1].0, snapshot.frontier[6][2].0, snapshot.frontier[6][3].0, snapshot.frontier[6][4].0, snapshot.frontier[6][5].0, snapshot.frontier[6][6].0, snapshot.frontier[6][7].0],
-            [snapshot.frontier[7][0].0, snapshot.frontier[7][1].0, snapshot.frontier[7][2].0, snapshot.frontier[7][3].0, snapshot.frontier[7][4].0, snapshot.frontier[7][5].0, snapshot.frontier[7][6].0, snapshot.frontier[7][7].0],
-            [snapshot.frontier[8][0].0, snapshot.frontier[8][1].0, snapshot.frontier[8][2].0, snapshot.frontier[8][3].0, snapshot.frontier[8][4].0, snapshot.frontier[8][5].0, snapshot.frontier[8][6].0, snapshot.frontier[8][7].0],
-            [snapshot.frontier[9][0].0, snapshot.frontier[9][1].0, snapshot.frontier[9][2].0, snapshot.frontier[9][3].0, snapshot.frontier[9][4].0, snapshot.frontier[9][5].0, snapshot.frontier[9][6].0, snapshot.frontier[9][7].0],
-            [snapshot.frontier[10][0].0, snapshot.frontier[10][1].0, snapshot.frontier[10][2].0, snapshot.frontier[10][3].0, snapshot.frontier[10][4].0, snapshot.frontier[10][5].0, snapshot.frontier[10][6].0, snapshot.frontier[10][7].0],
-            [snapshot.frontier[11][0].0, snapshot.frontier[11][1].0, snapshot.frontier[11][2].0, snapshot.frontier[11][3].0, snapshot.frontier[11][4].0, snapshot.frontier[11][5].0, snapshot.frontier[11][6].0, snapshot.frontier[11][7].0],
-            [snapshot.frontier[12][0].0, snapshot.frontier[12][1].0, snapshot.frontier[12][2].0, snapshot.frontier[12][3].0, snapshot.frontier[12][4].0, snapshot.frontier[12][5].0, snapshot.frontier[12][6].0, snapshot.frontier[12][7].0],
-            [snapshot.frontier[13][0].0, snapshot.frontier[13][1].0, snapshot.frontier[13][2].0, snapshot.frontier[13][3].0, snapshot.frontier[13][4].0, snapshot.frontier[13][5].0, snapshot.frontier[13][6].0, snapshot.frontier[13][7].0],
-            [snapshot.frontier[14][0].0, snapshot.frontier[14][1].0, snapshot.frontier[14][2].0, snapshot.frontier[14][3].0, snapshot.frontier[14][4].0, snapshot.frontier[14][5].0, snapshot.frontier[14][6].0, snapshot.frontier[14][7].0],
-            [snapshot.frontier[15][0].0, snapshot.frontier[15][1].0, snapshot.frontier[15][2].0, snapshot.frontier[15][3].0, snapshot.frontier[15][4].0, snapshot.frontier[15][5].0, snapshot.frontier[15][6].0, snapshot.frontier[15][7].0],
-            [snapshot.frontier[16][0].0, snapshot.frontier[16][1].0, snapshot.frontier[16][2].0, snapshot.frontier[16][3].0, snapshot.frontier[16][4].0, snapshot.frontier[16][5].0, snapshot.frontier[16][6].0, snapshot.frontier[16][7].0],
-            [snapshot.frontier[17][0].0, snapshot.frontier[17][1].0, snapshot.frontier[17][2].0, snapshot.frontier[17][3].0, snapshot.frontier[17][4].0, snapshot.frontier[17][5].0, snapshot.frontier[17][6].0, snapshot.frontier[17][7].0],
-            [snapshot.frontier[18][0].0, snapshot.frontier[18][1].0, snapshot.frontier[18][2].0, snapshot.frontier[18][3].0, snapshot.frontier[18][4].0, snapshot.frontier[18][5].0, snapshot.frontier[18][6].0, snapshot.frontier[18][7].0],
-            [snapshot.frontier[19][0].0, snapshot.frontier[19][1].0, snapshot.frontier[19][2].0, snapshot.frontier[19][3].0, snapshot.frontier[19][4].0, snapshot.frontier[19][5].0, snapshot.frontier[19][6].0, snapshot.frontier[19][7].0],
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[0]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[1]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[2]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[3]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[4]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[5]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[6]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[7]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[8]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[9]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[10]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[11]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[12]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[13]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[14]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[15]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[16]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[17]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[18]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[19]; [w0, w1, w2, w3, w4, w5, w6, w7] },
         ],
         empty: [
-            [empty[0][0].0, empty[0][1].0, empty[0][2].0, empty[0][3].0, empty[0][4].0, empty[0][5].0, empty[0][6].0, empty[0][7].0],
-            [empty[1][0].0, empty[1][1].0, empty[1][2].0, empty[1][3].0, empty[1][4].0, empty[1][5].0, empty[1][6].0, empty[1][7].0],
-            [empty[2][0].0, empty[2][1].0, empty[2][2].0, empty[2][3].0, empty[2][4].0, empty[2][5].0, empty[2][6].0, empty[2][7].0],
-            [empty[3][0].0, empty[3][1].0, empty[3][2].0, empty[3][3].0, empty[3][4].0, empty[3][5].0, empty[3][6].0, empty[3][7].0],
-            [empty[4][0].0, empty[4][1].0, empty[4][2].0, empty[4][3].0, empty[4][4].0, empty[4][5].0, empty[4][6].0, empty[4][7].0],
-            [empty[5][0].0, empty[5][1].0, empty[5][2].0, empty[5][3].0, empty[5][4].0, empty[5][5].0, empty[5][6].0, empty[5][7].0],
-            [empty[6][0].0, empty[6][1].0, empty[6][2].0, empty[6][3].0, empty[6][4].0, empty[6][5].0, empty[6][6].0, empty[6][7].0],
-            [empty[7][0].0, empty[7][1].0, empty[7][2].0, empty[7][3].0, empty[7][4].0, empty[7][5].0, empty[7][6].0, empty[7][7].0],
-            [empty[8][0].0, empty[8][1].0, empty[8][2].0, empty[8][3].0, empty[8][4].0, empty[8][5].0, empty[8][6].0, empty[8][7].0],
-            [empty[9][0].0, empty[9][1].0, empty[9][2].0, empty[9][3].0, empty[9][4].0, empty[9][5].0, empty[9][6].0, empty[9][7].0],
-            [empty[10][0].0, empty[10][1].0, empty[10][2].0, empty[10][3].0, empty[10][4].0, empty[10][5].0, empty[10][6].0, empty[10][7].0],
-            [empty[11][0].0, empty[11][1].0, empty[11][2].0, empty[11][3].0, empty[11][4].0, empty[11][5].0, empty[11][6].0, empty[11][7].0],
-            [empty[12][0].0, empty[12][1].0, empty[12][2].0, empty[12][3].0, empty[12][4].0, empty[12][5].0, empty[12][6].0, empty[12][7].0],
-            [empty[13][0].0, empty[13][1].0, empty[13][2].0, empty[13][3].0, empty[13][4].0, empty[13][5].0, empty[13][6].0, empty[13][7].0],
-            [empty[14][0].0, empty[14][1].0, empty[14][2].0, empty[14][3].0, empty[14][4].0, empty[14][5].0, empty[14][6].0, empty[14][7].0],
-            [empty[15][0].0, empty[15][1].0, empty[15][2].0, empty[15][3].0, empty[15][4].0, empty[15][5].0, empty[15][6].0, empty[15][7].0],
-            [empty[16][0].0, empty[16][1].0, empty[16][2].0, empty[16][3].0, empty[16][4].0, empty[16][5].0, empty[16][6].0, empty[16][7].0],
-            [empty[17][0].0, empty[17][1].0, empty[17][2].0, empty[17][3].0, empty[17][4].0, empty[17][5].0, empty[17][6].0, empty[17][7].0],
-            [empty[18][0].0, empty[18][1].0, empty[18][2].0, empty[18][3].0, empty[18][4].0, empty[18][5].0, empty[18][6].0, empty[18][7].0],
-            [empty[19][0].0, empty[19][1].0, empty[19][2].0, empty[19][3].0, empty[19][4].0, empty[19][5].0, empty[19][6].0, empty[19][7].0],
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[0]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[1]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[2]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[3]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[4]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[5]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[6]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[7]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[8]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[9]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[10]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[11]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[12]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[13]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[14]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[15]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[16]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[17]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[18]; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[19]; [w0, w1, w2, w3, w4, w5, w6, w7] },
         ],
     };
     match rec {
         Some(r) => {
             let r = *r;
-            w.recipient_owner = [r.owner_key[0].0, r.owner_key[1].0, r.owner_key[2].0, r.owner_key[3].0, r.owner_key[4].0, r.owner_key[5].0, r.owner_key[6].0, r.owner_key[7].0];
-            w.recipient_salt = [r.salt[0].0, r.salt[1].0, r.salt[2].0, r.salt[3].0, r.salt[4].0, r.salt[5].0, r.salt[6].0, r.salt[7].0];
+            w.recipient_owner = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = r.owner_key; [w0, w1, w2, w3, w4, w5, w6, w7] };
+            w.recipient_salt = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = r.salt; [w0, w1, w2, w3, w4, w5, w6, w7] };
             p.transfer = true;
             (w, p)
         },
```

Repair 12 times out at 240.915s (exit 124, 6,270,771,200 bytes peak, zero
swap); the unrolled projection body retains hundreds of trait-index shared
borrows. Each of the 72 eight-word projections now destructures the same
fixed-size Digest array into its eight M31 payloads. Array-pattern order
is exactly indices 0..7; every output word is identical. Patterns are
irrefutable for [M31;8] and add no panic/abort, allocation or I/O. All other
control flow/calls/fields are unchanged. Digest Copy uses field.rs:22;
no signature/type/other-function changes. This changes representation rather
than increasing timeout or memory for an unchanged failing job.

14. D277, restore disjoint bounded loops with digest patterns, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 4a23003366..7e5b3290af 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -235,52 +235,21 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let mut sibs = [[0u32; 8]; 24];
     bits[0] = u32::from(pair.selected_second);
     sibs[0] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = other; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[1] = ((pair.membership.index >> 0) & 1) as u32;
-    sibs[1] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[0]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[2] = ((pair.membership.index >> 1) & 1) as u32;
-    sibs[2] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[1]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[3] = ((pair.membership.index >> 2) & 1) as u32;
-    sibs[3] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[2]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[4] = ((pair.membership.index >> 3) & 1) as u32;
-    sibs[4] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[3]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[5] = ((pair.membership.index >> 4) & 1) as u32;
-    sibs[5] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[4]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[6] = ((pair.membership.index >> 5) & 1) as u32;
-    sibs[6] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[5]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[7] = ((pair.membership.index >> 6) & 1) as u32;
-    sibs[7] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[6]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[8] = ((pair.membership.index >> 7) & 1) as u32;
-    sibs[8] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[7]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[9] = ((pair.membership.index >> 8) & 1) as u32;
-    sibs[9] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[8]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[10] = ((pair.membership.index >> 9) & 1) as u32;
-    sibs[10] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[9]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[11] = ((pair.membership.index >> 10) & 1) as u32;
-    sibs[11] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[10]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[12] = ((pair.membership.index >> 11) & 1) as u32;
-    sibs[12] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[11]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[13] = ((pair.membership.index >> 12) & 1) as u32;
-    sibs[13] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[12]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[14] = ((pair.membership.index >> 13) & 1) as u32;
-    sibs[14] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[13]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[15] = ((pair.membership.index >> 14) & 1) as u32;
-    sibs[15] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[14]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[16] = ((pair.membership.index >> 15) & 1) as u32;
-    sibs[16] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[15]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[17] = ((pair.membership.index >> 16) & 1) as u32;
-    sibs[17] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[16]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[18] = ((pair.membership.index >> 17) & 1) as u32;
-    sibs[18] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[17]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[19] = ((pair.membership.index >> 18) & 1) as u32;
-    sibs[19] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[18]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[20] = ((pair.membership.index >> 19) & 1) as u32;
-    sibs[20] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.membership.siblings[19]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[21] = u32::from(input.super_root_directions[0]);
-    sibs[21] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = input.super_root_siblings[0]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[22] = u32::from(input.super_root_directions[1]);
-    sibs[22] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = input.super_root_siblings[1]; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    bits[23] = u32::from(input.super_root_directions[2]);
-    sibs[23] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = input.super_root_siblings[2]; [w0, w1, w2, w3, w4, w5, w6, w7] };
+    let mut level = 1;
+    while level < 21 {
+        bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
+        let sib = pair.membership.siblings[level - 1];
+        let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
+        sibs[level] = [w0, w1, w2, w3, w4, w5, w6, w7];
+        level += 1;
+    }
+    while level < 24 {
+        bits[level] = u32::from(input.super_root_directions[level - 21]);
+        let sib = input.super_root_siblings[level - 21];
+        let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
+        sibs[level] = [w0, w1, w2, w3, w4, w5, w6, w7];
+        level += 1;
+    }
     let empty = pair_empty_roots();
     let mut w = RW {
         input_value: pair.value,
@@ -303,50 +272,28 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
         transfer: false,
         asset: asset.0,
         next_pair_index: snapshot.next_pair_index,
-        frontier: [
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[0]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[1]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[2]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[3]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[4]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[5]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[6]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[7]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[8]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[9]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[10]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[11]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[12]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[13]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[14]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[15]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[16]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[17]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[18]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = snapshot.frontier[19]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        ],
-        empty: [
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[0]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[1]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[2]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[3]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[4]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[5]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[6]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[7]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[8]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[9]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[10]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[11]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[12]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[13]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[14]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[15]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[16]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[17]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[18]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = empty[19]; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        ],
+        frontier: {
+            let mut frontier = [[0u32; 8]; 20];
+            let mut l = 0;
+            while l < 20 {
+                let sib = snapshot.frontier[l];
+                let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
+                frontier[l] = [w0, w1, w2, w3, w4, w5, w6, w7];
+                l += 1;
+            }
+            frontier
+        },
+        empty: {
+            let mut roots = [[0u32; 8]; 20];
+            let mut l = 0;
+            while l < 20 {
+                let sib = empty[l];
+                let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
+                roots[l] = [w0, w1, w2, w3, w4, w5, w6, w7];
+                l += 1;
+            }
+            roots
+        },
     };
     match rec {
         Some(r) => {
```

Repair 13 times out at 240.541s, peak 6,342,434,816 bytes, zero swap,
with 486 MB LLBC. The replacement reduces expanded MIR by representing
levels 1..20 and 21..23 as ascending while loops again, and frontier/empty
indices 0..19 as ascending loops. Each loop writes exactly the previous
unrolled cell expression in the same order. The digest pattern is identical
for each cell. Counters terminate at 24 or 20 and cannot overflow; all array
indices and shift amounts are in bounds. No raw call or optional borrow
is carried through a loop. No returned value, panic/abort, allocation, I/O,
signature/type/other-function changes. Copy derives remain as recorded.
This differs from repair 5 by removing raw helper calls and their loans.

15. D277, destructure the fixed outer arrays and construct output literals,
verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 7e5b3290af..a6407c57cf 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -231,26 +231,64 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let snapshot = *snapshot;
     let pair = input.pair;
     let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
-    let mut bits = [0u32; 24];
-    let mut sibs = [[0u32; 8]; 24];
-    bits[0] = u32::from(pair.selected_second);
-    sibs[0] = { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = other; [w0, w1, w2, w3, w4, w5, w6, w7] };
-    let mut level = 1;
-    while level < 21 {
-        bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
-        let sib = pair.membership.siblings[level - 1];
-        let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
-        sibs[level] = [w0, w1, w2, w3, w4, w5, w6, w7];
-        level += 1;
-    }
-    while level < 24 {
-        bits[level] = u32::from(input.super_root_directions[level - 21]);
-        let sib = input.super_root_siblings[level - 21];
-        let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
-        sibs[level] = [w0, w1, w2, w3, w4, w5, w6, w7];
-        level += 1;
-    }
+    let [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20] = pair.membership.siblings;
+    let [s21, s22, s23] = input.super_root_siblings;
+    let [d0, d1, d2] = input.super_root_directions;
+    let bits = [
+        u32::from(pair.selected_second),
+        ((pair.membership.index >> 0) & 1) as u32,
+        ((pair.membership.index >> 1) & 1) as u32,
+        ((pair.membership.index >> 2) & 1) as u32,
+        ((pair.membership.index >> 3) & 1) as u32,
+        ((pair.membership.index >> 4) & 1) as u32,
+        ((pair.membership.index >> 5) & 1) as u32,
+        ((pair.membership.index >> 6) & 1) as u32,
+        ((pair.membership.index >> 7) & 1) as u32,
+        ((pair.membership.index >> 8) & 1) as u32,
+        ((pair.membership.index >> 9) & 1) as u32,
+        ((pair.membership.index >> 10) & 1) as u32,
+        ((pair.membership.index >> 11) & 1) as u32,
+        ((pair.membership.index >> 12) & 1) as u32,
+        ((pair.membership.index >> 13) & 1) as u32,
+        ((pair.membership.index >> 14) & 1) as u32,
+        ((pair.membership.index >> 15) & 1) as u32,
+        ((pair.membership.index >> 16) & 1) as u32,
+        ((pair.membership.index >> 17) & 1) as u32,
+        ((pair.membership.index >> 18) & 1) as u32,
+        ((pair.membership.index >> 19) & 1) as u32,
+        u32::from(d0),
+        u32::from(d1),
+        u32::from(d2),
+    ];
+    let sibs = [
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = other; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s1; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s2; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s3; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s4; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s5; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s6; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s7; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s8; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s9; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s10; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s11; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s12; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s13; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s14; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s15; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s16; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s17; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s18; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s19; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s20; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s21; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s22; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s23; [w0, w1, w2, w3, w4, w5, w6, w7] },
+    ];
     let empty = pair_empty_roots();
+    let [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19] = snapshot.frontier;
+    let [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, _] = empty;
     let mut w = RW {
         input_value: pair.value,
         output_value: out,
@@ -272,28 +310,50 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
         transfer: false,
         asset: asset.0,
         next_pair_index: snapshot.next_pair_index,
-        frontier: {
-            let mut frontier = [[0u32; 8]; 20];
-            let mut l = 0;
-            while l < 20 {
-                let sib = snapshot.frontier[l];
-                let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
-                frontier[l] = [w0, w1, w2, w3, w4, w5, w6, w7];
-                l += 1;
-            }
-            frontier
-        },
-        empty: {
-            let mut roots = [[0u32; 8]; 20];
-            let mut l = 0;
-            while l < 20 {
-                let sib = empty[l];
-                let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = sib;
-                roots[l] = [w0, w1, w2, w3, w4, w5, w6, w7];
-                l += 1;
-            }
-            roots
-        },
+        frontier: [
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f0; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f1; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f2; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f3; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f4; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f5; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f6; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f7; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f8; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f9; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f10; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f11; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f12; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f13; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f14; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f15; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f16; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f17; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f18; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f19; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        ],
+        empty: [
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e0; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e1; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e2; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e3; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e4; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e5; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e6; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e7; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e8; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e9; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e10; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e11; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e12; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e13; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e14; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e15; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e16; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e17; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e18; [w0, w1, w2, w3, w4, w5, w6, w7] },
+            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e19; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        ],
     };
     match rec {
         Some(r) => {
```

Repair 14 fails with Not_found in InterpReduceCollapse.ml:1991, called
from loop matching, exit 2 in 2.230s, 156,557,312 bytes, zero swap. This
replacement binds s1..s20 to exactly membership siblings 0..19, s21..s23
to exactly super siblings 0..2, d0..d2 to their directions, f0..f19 to
frontier 0..19, and e0..e19 to empty roots 0..19 (the 21st remains unused).
Bits and sibling literals list exactly the old ascending cells. Frontier
and empty literals list the same projected words. All patterns are
irrefutable for the fixed array lengths; no index/shift is out of bounds.
Destructuring and construction are pure Copy operations (M31 field.rs:22;
other Copy types as previously recorded). Empty-root evaluation and final
recipient branch remain; field computations may move across pure field
reads only. Same RW/RP and same panics/aborts; no new allocation or I/O.
No signature/type/other-function changes.

D277 final source repair: `b10f59dc07f0257f1cf0aecbc29aa1581462bb43`.
All three final ELFs MATCH at build cohort `16ff321691d1175826b6b046679ee49b4842c46f`;
see pv-runjoin15-20261027/gate-a.json. No later source change. The final
concrete helper closure fails preflight on unsupported pointer constants in
three poseidon2 functions outside records. Those functions and the extractor
remain unchanged; see pv-runjoin15-20261027/BLOCKER-D277.md. No accepted
R_shipped or identification is claimed.

16. D287: hoist empty-root computation to the single caller, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index a6407c57cf..1f3bea1dcc 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -225,7 +225,7 @@ include!("../../../../docs/research/v8-r0-zk-20261009/refine/diffharness/tests/g
 // ---------- the Wspend⁺ → record map on the Rust side ----------
 
 fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
-           chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
+           chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31, empty: [Digest; 21]) -> (RW, RP) {
     let input = *input;
     let chg = *chg;
     let snapshot = *snapshot;
@@ -286,7 +286,6 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
         { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s22; [w0, w1, w2, w3, w4, w5, w6, w7] },
         { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s23; [w0, w1, w2, w3, w4, w5, w6, w7] },
     ];
-    let empty = pair_empty_roots();
     let [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19] = snapshot.frontier;
     let [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, _] = empty;
     let mut w = RW {
@@ -401,7 +400,8 @@ impl CopyRecords {
         snapshot: &PoolV1PairLiveSnapshotV1,
         asset: M31,
     ) -> Self {
-        let (w, p) = records(input, out_value, recipient, change, snapshot, asset);
+        let empty = pair_empty_roots();
+        let (w, p) = records(input, out_value, recipient, change, snapshot, asset, empty);
         Self { w, p }
     }
 
```

The caller computes the same pair_empty_roots() exactly once and passes the
21-digest value by value. Digest is [M31; 8] (poseidon2.rs:60); M31
derives Copy at crates/aspis-core/src/field.rs:22, so the table and its
fixed arrays are Copy. The moved call crosses only pure, bounded field reads,
Copy destructuring and word construction in records; these cannot fail.
No allocation, I/O, hash, helper, other caller, or other function body is
changed. The caller only computes and passes the table. records contains
no hash or pair_empty_roots call. The explicit length 21 equals the shipped
POOL_V1_PAIR_TREE_DEPTH + 1 (20 + 1). Observable new behavior is unchanged.

17. D277 continued under D287, bounded word loops replace fixed array patterns, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index 1f3bea1dcc..feb49333ae 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -231,129 +231,51 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let snapshot = *snapshot;
     let pair = input.pair;
     let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
-    let [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20] = pair.membership.siblings;
-    let [s21, s22, s23] = input.super_root_siblings;
-    let [d0, d1, d2] = input.super_root_directions;
-    let bits = [
-        u32::from(pair.selected_second),
-        ((pair.membership.index >> 0) & 1) as u32,
-        ((pair.membership.index >> 1) & 1) as u32,
-        ((pair.membership.index >> 2) & 1) as u32,
-        ((pair.membership.index >> 3) & 1) as u32,
-        ((pair.membership.index >> 4) & 1) as u32,
-        ((pair.membership.index >> 5) & 1) as u32,
-        ((pair.membership.index >> 6) & 1) as u32,
-        ((pair.membership.index >> 7) & 1) as u32,
-        ((pair.membership.index >> 8) & 1) as u32,
-        ((pair.membership.index >> 9) & 1) as u32,
-        ((pair.membership.index >> 10) & 1) as u32,
-        ((pair.membership.index >> 11) & 1) as u32,
-        ((pair.membership.index >> 12) & 1) as u32,
-        ((pair.membership.index >> 13) & 1) as u32,
-        ((pair.membership.index >> 14) & 1) as u32,
-        ((pair.membership.index >> 15) & 1) as u32,
-        ((pair.membership.index >> 16) & 1) as u32,
-        ((pair.membership.index >> 17) & 1) as u32,
-        ((pair.membership.index >> 18) & 1) as u32,
-        ((pair.membership.index >> 19) & 1) as u32,
-        u32::from(d0),
-        u32::from(d1),
-        u32::from(d2),
-    ];
-    let sibs = [
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = other; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s1; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s2; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s3; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s4; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s5; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s6; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s7; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s8; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s9; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s10; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s11; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s12; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s13; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s14; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s15; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s16; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s17; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s18; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s19; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s20; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s21; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s22; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = s23; [w0, w1, w2, w3, w4, w5, w6, w7] },
-    ];
-    let [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19] = snapshot.frontier;
-    let [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, _] = empty;
     let mut w = RW {
-        input_value: pair.value,
-        output_value: out,
-        change_value: chg.value,
-        sk: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.nullifier_key; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        salt: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.salt; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        bits,
-        sibs,
-        pair_first: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.pair_leaf.first_commitment; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        pair_occupied: pair.pair_leaf.second_occupied.0,
-        pair_second: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = pair.pair_leaf.second_commitment; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
-        recipient_owner: ZERO8,
-        recipient_salt: ZERO8,
-        change_owner: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = chg.owner_key; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        change_salt: { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = chg.salt; [w0, w1, w2, w3, w4, w5, w6, w7] },
+        input_value: pair.value, output_value: out, change_value: chg.value,
+        sk: ZERO8, salt: ZERO8, bits: [0; 24], sibs: [[0; 8]; 24],
+        pair_first: ZERO8, pair_occupied: pair.pair_leaf.second_occupied.0,
+        pair_second: ZERO8, pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
+        recipient_owner: ZERO8, recipient_salt: ZERO8,
+        change_owner: ZERO8, change_salt: ZERO8,
     };
     let mut p = RP {
-        transfer: false,
-        asset: asset.0,
-        next_pair_index: snapshot.next_pair_index,
-        frontier: [
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f0; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f1; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f2; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f3; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f4; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f5; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f6; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f7; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f8; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f9; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f10; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f11; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f12; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f13; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f14; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f15; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f16; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f17; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f18; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = f19; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        ],
-        empty: [
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e0; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e1; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e2; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e3; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e4; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e5; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e6; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e7; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e8; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e9; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e10; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e11; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e12; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e13; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e14; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e15; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e16; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e17; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e18; [w0, w1, w2, w3, w4, w5, w6, w7] },
-            { let [M31(w0), M31(w1), M31(w2), M31(w3), M31(w4), M31(w5), M31(w6), M31(w7)] = e19; [w0, w1, w2, w3, w4, w5, w6, w7] },
-        ],
+        transfer: false, asset: asset.0, next_pair_index: snapshot.next_pair_index,
+        frontier: [[0; 8]; 20], empty: [[0; 8]; 20],
     };
+    w.bits[0] = u32::from(pair.selected_second);
+    let mut level = 1;
+    while level < 21 {
+        w.bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
+        level += 1;
+    }
+    while level < 24 {
+        w.bits[level] = u32::from(input.super_root_directions[level - 21]);
+        level += 1;
+    }
+    let mut j = 0;
+    while j < 8 {
+        w.sk[j] = pair.nullifier_key[j].0;
+        w.salt[j] = pair.salt[j].0;
+        w.sibs[0][j] = other[j].0;
+        w.pair_first[j] = pair.pair_leaf.first_commitment[j].0;
+        w.pair_second[j] = pair.pair_leaf.second_commitment[j].0;
+        w.change_owner[j] = chg.owner_key[j].0;
+        w.change_salt[j] = chg.salt[j].0;
+        let mut l = 0;
+        while l < 20 {
+            w.sibs[l + 1][j] = pair.membership.siblings[l][j].0;
+            p.frontier[l][j] = snapshot.frontier[l][j].0;
+            p.empty[l][j] = empty[l][j].0;
+            l += 1;
+        }
+        let mut l = 0;
+        while l < 3 {
+            w.sibs[l + 21][j] = input.super_root_siblings[l][j].0;
+            l += 1;
+        }
+        j += 1;
+    }
     match rec {
         Some(r) => {
             let r = *r;
```

The prior extraction has 642 array-read abort exits and 827,769 inserted
StorageDead nodes. panic=abort leaves that count unchanged, so no identical
Aeneas replay is attempted. Replace literal projection expansion with bounded
word loops. For every j in 0..8, write exactly the same digest word; the
inner l loops cover path levels 1..20 and 21..23, frontier/empty 0..19.
The bits loops cover exactly 1..20 and 21..23. All indices, additions and
shifts are bounded; counters cannot overflow. Initial zero cells are all
replaced by their old values before return; recipient match is byte-identical.
Writes are to disjoint private local cells and cross only total pure Copy
reads; the interleaving order of those writes is unobservable. No hash,
helper, allocation, I/O, signature or outside-records change. Copy derives
remain M31 field.rs:22, pair_trace.rs:71, pair_forest_trace.rs:53,
payment_relation.rs:88, pair_tree_profile.rs:403. Empty table is still passed
by value by the unchanged authorized D287 caller.

18. D277, local zero arrays instead of shared constant reads, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index e818b4735e..dc76132588 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -233,11 +233,11 @@ fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&Po
     let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
     let mut w = RW {
         input_value: pair.value, output_value: out, change_value: chg.value,
-        sk: ZERO8, salt: ZERO8, bits: [0; 24], sibs: [[0; 8]; 24],
-        pair_first: ZERO8, pair_occupied: pair.pair_leaf.second_occupied.0,
-        pair_second: ZERO8, pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
-        recipient_owner: ZERO8, recipient_salt: ZERO8,
-        change_owner: ZERO8, change_salt: ZERO8,
+        sk: [0u32; 8], salt: [0u32; 8], bits: [0; 24], sibs: [[0; 8]; 24],
+        pair_first: [0u32; 8], pair_occupied: pair.pair_leaf.second_occupied.0,
+        pair_second: [0u32; 8], pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
+        recipient_owner: [0u32; 8], recipient_salt: [0u32; 8],
+        change_owner: [0u32; 8], change_salt: [0u32; 8],
     };
     let mut p = RP {
         transfer: false, asset: asset.0, next_pair_index: snapshot.next_pair_index,
```

Aeneas 03 fails matching the first bit loop (248:4–251:5), carrying
eight shared loans from ZERO8 constant materialization. ZERO8 is exactly
[0u32; 8] at line 74. The literal constructs the identical Copy value
without that constant read. No other values, control, signature or
outside-records bytes change. u32 is Copy; M31 Copy remains field.rs:22.

19. D277, isolate pure loops in an owned-argument local closure, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index dc76132588..b3a65d1052 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -226,56 +226,58 @@ include!("../../../../docs/research/v8-r0-zk-20261009/refine/diffharness/tests/g
 
 fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
            chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31, empty: [Digest; 21]) -> (RW, RP) {
-    let input = *input;
-    let chg = *chg;
-    let snapshot = *snapshot;
-    let pair = input.pair;
-    let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
-    let mut w = RW {
-        input_value: pair.value, output_value: out, change_value: chg.value,
-        sk: [0u32; 8], salt: [0u32; 8], bits: [0; 24], sibs: [[0; 8]; 24],
-        pair_first: [0u32; 8], pair_occupied: pair.pair_leaf.second_occupied.0,
-        pair_second: [0u32; 8], pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
-        recipient_owner: [0u32; 8], recipient_salt: [0u32; 8],
-        change_owner: [0u32; 8], change_salt: [0u32; 8],
-    };
-    let mut p = RP {
-        transfer: false, asset: asset.0, next_pair_index: snapshot.next_pair_index,
-        frontier: [[0; 8]; 20], empty: [[0; 8]; 20],
-    };
-    w.bits[0] = u32::from(pair.selected_second);
-    let mut level = 1;
-    while level < 21 {
-        w.bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
-        level += 1;
-    }
-    while level < 24 {
-        w.bits[level] = u32::from(input.super_root_directions[level - 21]);
-        level += 1;
-    }
-    let mut j = 0;
-    while j < 8 {
-        w.sk[j] = pair.nullifier_key[j].0;
-        w.salt[j] = pair.salt[j].0;
-        w.sibs[0][j] = other[j].0;
-        w.pair_first[j] = pair.pair_leaf.first_commitment[j].0;
-        w.pair_second[j] = pair.pair_leaf.second_commitment[j].0;
-        w.change_owner[j] = chg.owner_key[j].0;
-        w.change_salt[j] = chg.salt[j].0;
-        let mut l = 0;
-        while l < 20 {
-            w.sibs[l + 1][j] = pair.membership.siblings[l][j].0;
-            p.frontier[l][j] = snapshot.frontier[l][j].0;
-            p.empty[l][j] = empty[l][j].0;
-            l += 1;
+    let (mut w, mut p) = (|input: PoolV1PairForestInputNoteWitnessV1,
+        out: u32, chg: PoolV1OutputNoteWitnessV1,
+        snapshot: PoolV1PairLiveSnapshotV1, asset: M31, empty: [Digest; 21]| {
+        let pair = input.pair;
+        let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
+        let mut w = RW {
+            input_value: pair.value, output_value: out, change_value: chg.value,
+            sk: [0u32; 8], salt: [0u32; 8], bits: [0; 24], sibs: [[0; 8]; 24],
+            pair_first: [0u32; 8], pair_occupied: pair.pair_leaf.second_occupied.0,
+            pair_second: [0u32; 8], pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
+            recipient_owner: [0u32; 8], recipient_salt: [0u32; 8],
+            change_owner: [0u32; 8], change_salt: [0u32; 8],
+        };
+        let mut p = RP {
+            transfer: false, asset: asset.0, next_pair_index: snapshot.next_pair_index,
+            frontier: [[0; 8]; 20], empty: [[0; 8]; 20],
+        };
+        w.bits[0] = u32::from(pair.selected_second);
+        let mut level = 1;
+        while level < 21 {
+            w.bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
+            level += 1;
         }
-        let mut l = 0;
-        while l < 3 {
-            w.sibs[l + 21][j] = input.super_root_siblings[l][j].0;
-            l += 1;
+        while level < 24 {
+            w.bits[level] = u32::from(input.super_root_directions[level - 21]);
+            level += 1;
         }
-        j += 1;
-    }
+        let mut j = 0;
+        while j < 8 {
+            w.sk[j] = pair.nullifier_key[j].0;
+            w.salt[j] = pair.salt[j].0;
+            w.sibs[0][j] = other[j].0;
+            w.pair_first[j] = pair.pair_leaf.first_commitment[j].0;
+            w.pair_second[j] = pair.pair_leaf.second_commitment[j].0;
+            w.change_owner[j] = chg.owner_key[j].0;
+            w.change_salt[j] = chg.salt[j].0;
+            let mut l = 0;
+            while l < 20 {
+                w.sibs[l + 1][j] = pair.membership.siblings[l][j].0;
+                p.frontier[l][j] = snapshot.frontier[l][j].0;
+                p.empty[l][j] = empty[l][j].0;
+                l += 1;
+            }
+            let mut l = 0;
+            while l < 3 {
+                w.sibs[l + 21][j] = input.super_root_siblings[l][j].0;
+                l += 1;
+            }
+            j += 1;
+        }
+        (w, p)
+    })(*input, out, *chg, *snapshot, asset, empty);
     match rec {
         Some(r) => {
             let r = *r;
```

Aeneas 04 still fails at first loop, InterpJoin.ml:2209 (0.704s).
The closure is inside records, captures nothing, accepts the same Copy
values by value, and contains the unchanged pure common record construction.
It returns (w,p) before the byte-identical recipient match. No heap
allocation or dynamic dispatch is used by this immediate noncapturing
closure call. This separates shared argument lifetimes from the loops without
changing signature, any other function body, values, ordering of observable
work or failure behavior. All reads/writes remain bounded as entry 17.
Copy locations remain field.rs:22, pair_trace.rs:71, pair_forest_trace.rs:53,
payment_relation.rs:88 and pair_tree_profile.rs:403.

20. Stop closure route and copy loop fields before direct loops, verbatim:

```diff
diff --git a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
index b3a65d1052..2a6ceb7585 100644
--- a/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
+++ b/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs
@@ -226,58 +226,67 @@ include!("../../../../docs/research/v8-r0-zk-20261009/refine/diffharness/tests/g
 
 fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
            chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31, empty: [Digest; 21]) -> (RW, RP) {
-    let (mut w, mut p) = (|input: PoolV1PairForestInputNoteWitnessV1,
-        out: u32, chg: PoolV1OutputNoteWitnessV1,
-        snapshot: PoolV1PairLiveSnapshotV1, asset: M31, empty: [Digest; 21]| {
-        let pair = input.pair;
-        let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
-        let mut w = RW {
-            input_value: pair.value, output_value: out, change_value: chg.value,
-            sk: [0u32; 8], salt: [0u32; 8], bits: [0; 24], sibs: [[0; 8]; 24],
-            pair_first: [0u32; 8], pair_occupied: pair.pair_leaf.second_occupied.0,
-            pair_second: [0u32; 8], pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
-            recipient_owner: [0u32; 8], recipient_salt: [0u32; 8],
-            change_owner: [0u32; 8], change_salt: [0u32; 8],
-        };
-        let mut p = RP {
-            transfer: false, asset: asset.0, next_pair_index: snapshot.next_pair_index,
-            frontier: [[0; 8]; 20], empty: [[0; 8]; 20],
-        };
-        w.bits[0] = u32::from(pair.selected_second);
-        let mut level = 1;
-        while level < 21 {
-            w.bits[level] = ((pair.membership.index >> (level - 1)) & 1) as u32;
-            level += 1;
-        }
-        while level < 24 {
-            w.bits[level] = u32::from(input.super_root_directions[level - 21]);
-            level += 1;
+    let input = *input;
+    let chg = *chg;
+    let snapshot = *snapshot;
+    let pair = input.pair;
+    let membership_index = pair.membership.index;
+    let directions = input.super_root_directions;
+    let key = pair.nullifier_key;
+    let salt = pair.salt;
+    let first = pair.pair_leaf.first_commitment;
+    let second = pair.pair_leaf.second_commitment;
+    let owner = chg.owner_key;
+    let change_salt = chg.salt;
+    let siblings = pair.membership.siblings;
+    let frontier = snapshot.frontier;
+    let supers = input.super_root_siblings;
+    let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
+    let mut w = RW {
+        input_value: pair.value, output_value: out, change_value: chg.value,
+        sk: [0u32; 8], salt: [0u32; 8], bits: [0; 24], sibs: [[0; 8]; 24],
+        pair_first: [0u32; 8], pair_occupied: pair.pair_leaf.second_occupied.0,
+        pair_second: [0u32; 8], pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
+        recipient_owner: [0u32; 8], recipient_salt: [0u32; 8],
+        change_owner: [0u32; 8], change_salt: [0u32; 8],
+    };
+    let mut p = RP {
+        transfer: false, asset: asset.0, next_pair_index: snapshot.next_pair_index,
+        frontier: [[0; 8]; 20], empty: [[0; 8]; 20],
+    };
+    w.bits[0] = u32::from(pair.selected_second);
+    let mut level = 1;
+    while level < 21 {
+        w.bits[level] = ((membership_index >> (level - 1)) & 1) as u32;
+        level += 1;
+    }
+    while level < 24 {
+        w.bits[level] = u32::from(directions[level - 21]);
+        level += 1;
+    }
+    let mut j = 0;
+    while j < 8 {
+        w.sk[j] = key[j].0;
+        w.salt[j] = salt[j].0;
+        w.sibs[0][j] = other[j].0;
+        w.pair_first[j] = first[j].0;
+        w.pair_second[j] = second[j].0;
+        w.change_owner[j] = owner[j].0;
+        w.change_salt[j] = change_salt[j].0;
+        let mut l = 0;
+        while l < 20 {
+            w.sibs[l + 1][j] = siblings[l][j].0;
+            p.frontier[l][j] = frontier[l][j].0;
+            p.empty[l][j] = empty[l][j].0;
+            l += 1;
         }
-        let mut j = 0;
-        while j < 8 {
-            w.sk[j] = pair.nullifier_key[j].0;
-            w.salt[j] = pair.salt[j].0;
-            w.sibs[0][j] = other[j].0;
-            w.pair_first[j] = pair.pair_leaf.first_commitment[j].0;
-            w.pair_second[j] = pair.pair_leaf.second_commitment[j].0;
-            w.change_owner[j] = chg.owner_key[j].0;
-            w.change_salt[j] = chg.salt[j].0;
-            let mut l = 0;
-            while l < 20 {
-                w.sibs[l + 1][j] = pair.membership.siblings[l][j].0;
-                p.frontier[l][j] = snapshot.frontier[l][j].0;
-                p.empty[l][j] = empty[l][j].0;
-                l += 1;
-            }
-            let mut l = 0;
-            while l < 3 {
-                w.sibs[l + 21][j] = input.super_root_siblings[l][j].0;
-                l += 1;
-            }
-            j += 1;
+        let mut l = 0;
+        while l < 3 {
+            w.sibs[l + 21][j] = supers[l][j].0;
+            l += 1;
         }
-        (w, p)
-    })(*input, out, *chg, *snapshot, asset, empty);
+        j += 1;
+    }
     match rec {
         Some(r) => {
             let r = *r;
```

Closure extraction 06 fails outside records at core::ops::function
FnOnce::call_once (function.rs:250:4–250:70), FunsAnalysis.ml:134: called
function missing from crate. That route is stopped; no helper or extractor
is modified. This change removes the closure entirely, restoring direct
record construction from repair 18, and captures every source field read
by a loop before entering any loop. These are identical Copy values, with
Copy derives at field.rs:22, pair_trace.rs:71, pair_forest_trace.rs:53,
payment_relation.rs:88, pair_tree_profile.rs:403. The membership index is
now expanded before the first loop instead of during its first iteration,
which targets the observed context mismatch. No values, loop bounds,
recipient handling, failure behavior, signature, allocation, I/O or bytes
outside records change. D287 caller remains identical.
