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
