# PIN2 W3c: discriminant-instance clash fix in the overlay copy of the PIN2 emissions

Symptom (W4, and W3c C0529/C0714): importing `PIN2_NEWGATE_r0` together with the gate module
`AspisR1FinishRelationCurrent.Types` fails with "environment already contains
'instDiscriminantErrorIsize'". Cause: Aeneas's `@[discriminant isize]` attribute elaborates an
anonymous `instance` whose auto-generated name lands at top level (`instDiscriminant<Ty>Isize`), and
two separately compiled modules both carry `instDiscriminantErrorIsize`. Lean disambiguates such
names only inside one environment (suffix `_1`), not across imports.

Fix (Lean side only, the gate is untouched): in the overlay copies of `PIN2_NEWGATE_r0` and
`PIN2_NEWGATE_r1_semantic`, each `@[discriminant isize]` attribute is removed and replaced, right
after its inductive, by exactly what the attribute generates: the definition
`<Ty>.read_discriminant` (values 0..n-1 in constructor order, as the attribute assigns without an
explicit list) and an instance of `Aeneas.Std.Discriminant <Ty> Std.Isize`, now explicitly named and
declared inside `namespace AspisR1PublicPreparationPIN2`:

| emission | type | new instance name (in AspisR1PublicPreparationPIN2) |
| --- | --- | --- |
| r0 | aspis_core.state_only_prefix.r0.Error | instDiscriminant_PIN2_r0_StateOnlyPrefixError_Isize |
| r0 | pool_v1.pair_forest_semantic_terminal.CompiledVariant | instDiscriminant_PIN2_r0_CompiledVariant_Isize |
| r0 | pool_v1.pair_forest_semantic_terminal.r0.Public | instDiscriminant_PIN2_r0_Public_Isize |
| r1_semantic | r1_wire.Error | instDiscriminant_PIN2_r1_WireError_Isize |

Only the first clashes today; the other three were named the same way because each would collide
with the next gate module that carries the same attribute on a same-named type. Neither emission
uses `read_discriminant` or the instances anywhere. No other line changed. The text from
`def pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes` to the end of the r0 file is
byte-identical (42,518 bytes, sha256 prefix 19015aca48f26f74 before and after), and so is every
function before it.

For Stream C's next emission: post-process every `@[discriminant ...]` the same way, or emit the
types inside a namespace and name the instance explicitly.

## Hashes (sha256)

| file | Stream C (before) | W3c overlay copy (after) |
| --- | --- | --- |
| PIN2_NEWGATE_r0.lean | 92162163ae5b4017ab10217fa1d8d47e22ff0177013b30511e6bc5cea7798bfb | 949d0070883f92f9ae9a0a49c57c165a1feec4a430334602f2897471f61488bd |
| PIN2_NEWGATE_r0.olean | f9ade0b9e07a69230a034a24118be5152b9eff22b1ff9cdc205b1e8ca40c94c9 | 0c29efc89f6dab8c21bd0fc4f00d9ab97e466c659e7f1cdbd9429c59a7ed054d (C1321) |
| PIN2_NEWGATE_r1_semantic.lean | b5ff0038fb968bbde2621ebb0b69e8e5227b6d4cfb54a2c6a21d4dca523f9aff | b0a096b056f8c68bf64832a97cb1c65c5d09e771eca992304ee9ef75c7390fc6 |
| PIN2_NEWGATE_r1_semantic.olean | 7b590c58d7ae8415fca7e4237e646d4fef0f626867c7559ab436d32e7012f661 | c89ff3f196902271cb3a81c6ce4a02834fdb2d7c1e84ad0b9030d12dcce20685 (C1322) |

The Stream C originals are kept as `release-originals/PIN2_NEWGATE_r0.streamC.lean` and
`release-originals/PIN2_NEWGATE_r1_semantic.streamC.lean`. Every overlay object that imports either
emission (transitively) is stale after this change and is rebuilt in import order (list in
`FORCE-REBUILD-1.txt`).

## Unified diffs
```diff
--- release-originals/PIN2_NEWGATE_r0.streamC.lean	2026-11-11 08:13:32
+++ sources/PIN2_NEWGATE_r0.lean	2026-11-11 08:13:33
@@ -82,7 +82,6 @@
     Source: 'crates/aspis-core/src/state_only_prefix.rs', lines 1629:4-1629:18
     Name pattern: [aspis_core::state_only_prefix::r0::Error]
     Visibility: public -/
-@[discriminant isize]
 inductive aspis_core.state_only_prefix.r0.Error where
 | Allocation : aspis_core.state_only_prefix.r0.Error
 | RowOrder : Std.U8 → Std.U8 → aspis_core.state_only_prefix.r0.Error
@@ -96,13 +95,47 @@
 | TrailingBytes : aspis_core.state_only_prefix.r0.Error
 | Public : aspis_core.state_only_prefix.r0.Error
 
+/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
+   attribute generates plus an explicitly named instance inside this namespace, so the
+   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
+   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
+   constructor order, as the attribute assigns. -/
+def aspis_core.state_only_prefix.r0.Error.read_discriminant (x : aspis_core.state_only_prefix.r0.Error) : Std.Isize :=
+  match x with
+  | .Allocation => 0#isize
+  | .RowOrder _ _ => 1#isize
+  | .InvalidRow => 2#isize
+  | .Tag _ => 3#isize
+  | .Length _ => 4#isize
+  | .NonCanonical _ _ => 5#isize
+  | .Boundary _ => 6#isize
+  | .Terminal => 7#isize
+  | .EqualCirclePoints => 8#isize
+  | .TrailingBytes => 9#isize
+  | .Public => 10#isize
+
+instance instDiscriminant_PIN2_r0_StateOnlyPrefixError_Isize : Aeneas.Std.Discriminant aspis_core.state_only_prefix.r0.Error Std.Isize where
+  read_discriminant := aspis_core.state_only_prefix.r0.Error.read_discriminant
+
 /-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::CompiledVariant]
     Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 81:0-84:1 -/
-@[discriminant isize]
 inductive pool_v1.pair_forest_semantic_terminal.CompiledVariant where
 | PrivateTransfer : pool_v1.pair_forest_semantic_terminal.CompiledVariant
 | Withdrawal : pool_v1.pair_forest_semantic_terminal.CompiledVariant
 
+/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
+   attribute generates plus an explicitly named instance inside this namespace, so the
+   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
+   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
+   constructor order, as the attribute assigns. -/
+def pool_v1.pair_forest_semantic_terminal.CompiledVariant.read_discriminant (x : pool_v1.pair_forest_semantic_terminal.CompiledVariant) : Std.Isize :=
+  match x with
+  | .PrivateTransfer => 0#isize
+  | .Withdrawal => 1#isize
+
+instance instDiscriminant_PIN2_r0_CompiledVariant_Isize : Aeneas.Std.Discriminant pool_v1.pair_forest_semantic_terminal.CompiledVariant Std.Isize where
+  read_discriminant := pool_v1.pair_forest_semantic_terminal.CompiledVariant.read_discriminant
+
 /-- [aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1]
     Source: 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 404:0-411:1
     Visibility: public -/
@@ -174,7 +207,6 @@
 /-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public]
     Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 1999:4-2008:5
     Visibility: public -/
-@[discriminant isize]
 inductive pool_v1.pair_forest_semantic_terminal.r0.Public where
 | Transfer :
   pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
@@ -185,9 +217,22 @@
   pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
   pool_v1.pair_forest_semantic_terminal.r0.Public
 
+/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
+   attribute generates plus an explicitly named instance inside this namespace, so the
+   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
+   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
+   constructor order, as the attribute assigns. -/
+def pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant (x : pool_v1.pair_forest_semantic_terminal.r0.Public) : Std.Isize :=
+  match x with
+  | .Transfer _ _ => 0#isize
+  | .Withdrawal _ _ => 1#isize
 
+instance instDiscriminant_PIN2_r0_Public_Isize : Aeneas.Std.Discriminant pool_v1.pair_forest_semantic_terminal.r0.Public Std.Isize where
+  read_discriminant := pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant
 
 
+
+
 /-- [aspis_core::field::P]
     Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:16
     Name pattern: [aspis_core::field::P]
--- release-originals/PIN2_NEWGATE_r1_semantic.streamC.lean	2026-11-11 08:13:32
+++ sources/PIN2_NEWGATE_r1_semantic.lean	2026-11-11 08:13:33
@@ -53,7 +53,6 @@
 /-- [aspis_r1_cost_probe::r1_wire::Error]
     Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 24:0-36:1
     Visibility: public -/
-@[discriminant isize]
 inductive r1_wire.Error where
 | Allocation : r1_wire.Error
 | RowOrder : Std.U8 → Std.U8 → r1_wire.Error
@@ -67,6 +66,28 @@
 | TrailingBytes : r1_wire.Error
 | Public : r1_wire.Error
 
+/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
+   attribute generates plus an explicitly named instance inside this namespace, so the
+   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
+   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
+   constructor order, as the attribute assigns. -/
+def r1_wire.Error.read_discriminant (x : r1_wire.Error) : Std.Isize :=
+  match x with
+  | .Allocation => 0#isize
+  | .RowOrder _ _ => 1#isize
+  | .InvalidRow => 2#isize
+  | .Tag _ => 3#isize
+  | .Length _ => 4#isize
+  | .NonCanonical _ _ => 5#isize
+  | .Boundary _ => 6#isize
+  | .Terminal => 7#isize
+  | .EqualCirclePoints => 8#isize
+  | .TrailingBytes => 9#isize
+  | .Public => 10#isize
+
+instance instDiscriminant_PIN2_r1_WireError_Isize : Aeneas.Std.Discriminant r1_wire.Error Std.Isize where
+  read_discriminant := r1_wire.Error.read_discriminant
+
 /-- [aspis_r1_cost_probe::r1_wire::SemanticTranscript]
     Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 172:0-176:1
     Visibility: public -/
```
