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
