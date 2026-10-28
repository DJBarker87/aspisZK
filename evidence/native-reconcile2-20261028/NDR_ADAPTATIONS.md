# Observer reconciliation

NDR_L001 validates the first adaptation with standard axioms only (3.800 s,
3,841,008 KiB RSS, swap 0). No cryptographic or adaptive execution premise is
discharged.

## NDO_JGi_FinishFields.source

Before: `(obs : Option (verifier.Phase → Result Unit))`, with premise
`FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)`.
After: `(obs : Option (RPz7_PhaseIso.Phase → Result Unit))`, with the identical
premise and conclusion. `NDO_PhaseIdentity.retainedCarrier` identifies this
carrier with the historical FirstCaller.Phase; the imported producer's nominal
verifier.Phase is distinct. All other quantifiers and proof bytes are unchanged.
This restores the historical quantification; it does not transport an execution
from the producer carrier. New direct import: NDO_PhaseIdentity.

The remaining adaptations and the 23 upstream differences are tracked below
as validation advances. Non-None producer observers require a proved execution
transport at producer/model comparison boundaries; callback round trips alone
are not that transport. No such new adaptive execution result is claimed.

## The 23 upstream body differences

These selected replay modules are reused unchanged, rather than copied or patched.
The carrier change is `verifier.Phase` (historical alias) → `RPz7_PhaseIso.Phase`
(retained FirstCaller carrier), except the two special cases stated below.
No theorem conclusion or non-observer quantifier is deliberately changed.

- `AuS1_Semantic3` → `RPz7_AuS1_Semantic3`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `ClaimsUnrolledFinish` → `RPz7_ClaimsUnrolledFinish`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `F3U_VerifyHead` → `RPz8_F3U_VerifyHead`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `F3V_SemanticFinish` → `RPz7_F3V_SemanticFinish`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `F3V_SemanticVerify` → `RPz7_F3V_SemanticVerify`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `FIr_FinishComparison` → `RPx_FIr_FinishComparison`: FinishModel calls/proof applications change `obs` → `RPz7_PhaseIso.observerToFirst obs`. A callback map is explicit; this is not a new adaptive execution proof.
- `GExp_FinishAssociation` → `RPz7_GExp_FinishAssociation`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `GExp_VerifyAssociation` → `RPz7_GExp_VerifyAssociation`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `RawJ_VerifyRead` → `RPz8_RawJ_VerifyRead`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `RawK_VerifyHead` → `RPz8_RawK_VerifyHead`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1AcceptedChallengesNumericV1` → `RPz7_S1AcceptedChallengesNumericV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1AcceptedSemanticNumericV1` → `RPz7_S1AcceptedSemanticNumericV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticBudgetV1` → `RPz7_S1SemanticBudgetV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeFinishExactV1` → `RPz7_S1SemanticCodeFinishExactV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeFinishV1` → `RPz7_S1SemanticCodeFinishV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeVerifyExactV1` → `RPz7_S1SemanticCodeVerifyExactV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeVerifyV1` → `RPz7_S1SemanticCodeVerifyV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticFinishBoundsV1` → `RPz7_S1SemanticFinishBoundsV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticFinishModelV1` → `RPz7_S1SemanticFinishModelV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticFinishRootsV1` → `RPz7_S1SemanticFinishRootsV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticPhaseV1` → `RPz7_S1SemanticPhaseV1`: Historical alias `verifier.Phase := FirstCaller.Phase` moves to retained `RPz7_PhaseIso.Phase`; no producer carrier equality.
- `S1SemanticPrefixModelV1` → `RPz7_S1SemanticPrefixModelV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticVerifyReachabilityV1` → `RPz7_S1SemanticVerifyReachabilityV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.

## NDO_JGi_ClaimArrays.source and NDO_JHm_SemanticOperands.source

Both theorem statements remain byte-identical. In each proof's application of
JGi_FinishFields.source, the inferred/explicit `none` observer becomes
`RPz7_PhaseIso.observerToFirst none`; the existing finish premise is supplied by
`by simpa only [NDO_PhaseIdentity.noneToFirst] using finish` (respectively
`finished`). This is the release None specialization, without a producer
execution transport assumption. These edits await dependency-ordered compilation.

NDO_JHk_QueryPowerStep's observer remains the emitted producer carrier: its
query-values theorem calls the producer API directly. NDO_JGy_QueryFrontier and
NDO_JHc_WriterContinuation use producer marks and None directly; no semantic
FinishModel boundary occurs there and their statements/bodies remain unchanged.

## Exact upstream before/after observer statement excerpts

Minus lines are historical; plus lines are selected replay. Context preserves
the affected premise/conclusion. This is a source inventory, not new proof credit.

```diff
### AuS1_Semantic3 -> RPz7_AuS1_Semantic3
--- lean/AuS1_Semantic3.lean
+++ evidence/replay-dry8-20261026/RPz7_AuS1_Semantic3.lean
@@ -24,5 +24,5 @@
     (law : ∀ h parts, D.digest h parts = hashv parts) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
     (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
-    (obs : Option (verifier.Phase → Result Unit)) :
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
     Uniform hashv (finish R B D pub prefix1 transcript challenges obs) := by
   unfold finish
@@ -40,5 +40,5 @@
     (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
     (law : ∀ h parts, D.digest h parts = hashv parts) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
-    (obs : Option (verifier.Phase → Result Unit)) :
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
     Uniform hashv (verify (finish R B) D pub bytes hash obs) := by
   unfold verify
```

```diff
### ClaimsUnrolledFinish -> RPz7_ClaimsUnrolledFinish
--- docs/research/100bit-spend-path-20261013/lean/ClaimsUnrolledFinish.lean
+++ evidence/replay-dry8-20261026/RPz7_ClaimsUnrolledFinish.lean
@@ -2,5 +2,4 @@
 import RPz7_S1ExtractedRoundChildrenV1
 import RPz7_S1SemanticFinishBoundsV1
-
 /-! Install the complete emitted finite Claims VALUE interpretation in the
 actual S1 finish consumer. Source getters and the existing full indexed decoder
@@ -124,5 +123,5 @@
     (pre : MainPrefix) (before : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
     (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
-    (obs : Option (AspisR1PublicPreparation.verifier.Phase → Result Unit))
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
     (out : AspisR1PublicPreparation.r1_semantic.Verified H)
     (accepted : AspisR1PublicPreparation.FinishModel.finish R (install std B)
```

```diff
### F3U_VerifyHead -> RPz8_F3U_VerifyHead
--- lean/F3U_VerifyHead.lean
+++ evidence/replay-dry9-20261027/RPz8_F3U_VerifyHead.lean
@@ -10,5 +10,5 @@
 theorem first (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
-    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
     (success : erase (S1SemanticCode.verify F D pub input hash obs) = ok (.Ok out)) :
     ∃ (encoded : alloc.vec.Vec U8) (root state : State),
```

```diff
### F3V_SemanticFinish -> RPz7_F3V_SemanticFinish
--- lean/F3V_SemanticFinish.lean
+++ evidence/replay-dry8-20261026/RPz7_F3V_SemanticFinish.lean
@@ -13,5 +13,5 @@
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
     (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Hash)
-    (ch : r1_wire.Challenges) (obs : Option (verifier.Phase → Result Unit)) :
+    (ch : r1_wire.Challenges) (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
     F3U_Rehash.code H (S1SemanticCode.finish R B D pub p t ch obs)=
       S1SemanticCode.finish R B (F3U_Rehash.dictionary H D) pub p t ch obs := by
```

```diff
### F3V_SemanticVerify -> RPz7_F3V_SemanticVerify
--- lean/F3V_SemanticVerify.lean
+++ evidence/replay-dry8-20261026/RPz7_F3V_SemanticVerify.lean
@@ -13,5 +13,5 @@
     (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
-    (bytes : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit)) :
+    (bytes : Slice U8) (hash : Hash) (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
     F3U_Rehash.code H (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes hash obs)=
       S1SemanticCode.verify (S1SemanticCode.finish R B) (F3U_Rehash.dictionary H D) pub bytes hash obs := by
```

```diff
### FIr_FinishComparison -> RPx_FIr_FinishComparison
--- lean/FIr_FinishComparison.lean
+++ evidence/replay-deployed2-20261027/RPx_FIr_FinishComparison.lean
@@ -42,5 +42,5 @@
     (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
     (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
-    (hfinish : FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)) :
+    (hfinish : FinishModel.finish R B D pub pre before challenges (RPz7_PhaseIso.observerToFirst obs) = ok (.Ok out)) :
     ∃ running afterRounds terminal mask16 mask10 claim0 claim27 mask
         etaTerminal masked extra28,
@@ -59,5 +59,5 @@
       hrounds, hchallenges, hstate, htranscript, hclaims, hrecord25, hextra,
       hcircle25, hrecord26, hbeforeZ1, hcircle26, hz⟩ :=
-    S1SemanticFinishBounds.finish_success R B D pub pre before challenges obs out hfinish
+    S1SemanticFinishBounds.finish_success R B D pub pre before challenges (RPz7_PhaseIso.observerToFirst obs) out hfinish
   have h := hfinish
   unfold FinishModel.finish at h
```

```diff
### GExp_FinishAssociation -> RPz7_GExp_FinishAssociation
--- lean/GExp_FinishAssociation.lean
+++ evidence/replay-dry8-20261026/RPz7_GExp_FinishAssociation.lean
@@ -10,5 +10,5 @@
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
     (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
-    (obs : Option (verifier.Phase → Result Unit)) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
     (law : ∀ h parts, D.digest h parts = hashv parts) :
     AspisR1.SdkD_PrepareLower.Associated hashv (finish R B D pub prefix1 transcript challenges obs) := by
```

```diff
### GExp_VerifyAssociation -> RPz7_GExp_VerifyAssociation
--- lean/GExp_VerifyAssociation.lean
+++ evidence/replay-dry8-20261026/RPz7_GExp_VerifyAssociation.lean
@@ -9,5 +9,5 @@
 theorem verify_associated (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
-    (obs : Option (verifier.Phase → Result Unit)) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
     (law : ∀ h parts, D.digest h parts = hashv parts) :
     AspisR1.SdkD_PrepareLower.Associated hashv (verify (finish R B) D pub bytes hash obs) := by
```

```diff
### RawJ_VerifyRead -> RPz8_RawJ_VerifyRead
--- lean/RawJ_VerifyRead.lean
+++ evidence/replay-dry9-20261027/RPz8_RawJ_VerifyRead.lean
@@ -10,5 +10,5 @@
 theorem frame (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
-    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
     (success : erase (S1SemanticCode.verify F D pub input hash obs) = ok (.Ok out)) :
     ∃ p, PrefixAdapter.parseAccepted input = ok (.Ok p) ∧
```

```diff
### RawK_VerifyHead -> RPz8_RawK_VerifyHead
--- lean/RawK_VerifyHead.lean
+++ evidence/replay-dry9-20261027/RPz8_RawK_VerifyHead.lean
@@ -10,5 +10,5 @@
 theorem first (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
-    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
     (success : erase (S1SemanticCode.verify F D pub input hash obs) = ok (.Ok out)) :
     ∃ entry, RawK_Head.head (S1SemanticCode.verify F D pub input hash obs) = some entry ∧
```

```diff
### S1AcceptedChallengesNumericV1 -> RPz7_S1AcceptedChallengesNumericV1
--- evidence/replay-dry3-20261026/RPz2_recovered/S1AcceptedChallengesNumericV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1AcceptedChallengesNumericV1.lean
@@ -14,5 +14,5 @@
 theorem accepted_verify_challenges {H : Type} (B : FinishModel.Boundaries)
     (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
-    (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
+    (bytes : Slice U8) (hash : H) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
     (out : r1_semantic.Verified H)
     (accepted : VerifyPrefix.verify (FinishModel.finish children B) D pub bytes hash obs = ok (.Ok out)) :
```

```diff
### S1AcceptedSemanticNumericV1 -> RPz7_S1AcceptedSemanticNumericV1
--- evidence/replay-dry3-20261026/RPz2_recovered/S1AcceptedSemanticNumericV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1AcceptedSemanticNumericV1.lean
@@ -21,5 +21,5 @@
     (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
     (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H)
-    (challenges : r1_wire.Challenges) (obs : Option (verifier.Phase → Result Unit))
+    (challenges : r1_wire.Challenges) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
     (out : r1_semantic.Verified H)
     (accepted : FinishModel.finish children B D pub pre before challenges obs = ok (.Ok out)) :
@@ -42,5 +42,5 @@
 theorem accepted_verify_numeric {H : Type} (B : FinishModel.Boundaries)
     (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
-    (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
+    (bytes : Slice U8) (hash : H) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
     (out : r1_semantic.Verified H)
     (accepted : VerifyPrefix.verify (FinishModel.finish children B) D pub bytes hash obs = ok (.Ok out)) :
```

```diff
### S1SemanticBudgetV1 -> RPz7_S1SemanticBudgetV1
--- evidence/global-exp-20261026/GExp_029/sources/S1SemanticBudgetV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticBudgetV1.lean
@@ -220,5 +220,5 @@
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
     (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
-    (obs : Option (verifier.Phase → Result Unit)) : bounded 36 (finish R B D pub prefix1 transcript challenges obs) := by
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) : bounded 36 (finish R B D pub prefix1 transcript challenges obs) := by
   unfold finish
   repeat' first
@@ -243,5 +243,5 @@
 theorem verify_bounded (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
-    (obs : Option (verifier.Phase → Result Unit)) : bounded 82 (verify (finish R B) D pub bytes hash obs) := by
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) : bounded 82 (verify (finish R B) D pub bytes hash obs) := by
   unfold verify
   repeat' first
```

```diff
### S1SemanticCodeFinishExactV1 -> RPz7_S1SemanticCodeFinishExactV1
--- evidence/sdk-child2-20261026/SdkD_091/sources/S1SemanticCodeFinishExactV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticCodeFinishExactV1.lean
@@ -15,5 +15,5 @@
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
     (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
-    (obs : Option (verifier.Phase → Result Unit)) :
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
     erase (finish R B D pub prefix1 transcript challenges obs)=FinishModel.finish R B D pub prefix1 transcript challenges obs := by
   unfold finish FinishModel.finish
```

```diff
### S1SemanticCodeFinishV1 -> RPz7_S1SemanticCodeFinishV1
--- evidence/sdk-child2-20261026/SdkD_081/sources/S1SemanticCodeFinishV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticCodeFinishV1.lean
@@ -13,5 +13,5 @@
   (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
   (challenges : r1_wire.Challenges)
-  (obs : Option (verifier.Phase → Result Unit)) :
+  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
   Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
   := do
```

```diff
### S1SemanticCodeVerifyExactV1 -> RPz7_S1SemanticCodeVerifyExactV1
--- evidence/sdk-child2-20261026/SdkD_095/sources/S1SemanticCodeVerifyExactV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticCodeVerifyExactV1.lean
@@ -18,5 +18,5 @@
     {H : Type} (D : aspis_core.Digest32 H)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
-    (obs : Option (verifier.Phase → Result Unit)) :
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
     erase (verify (finish R B) D pub bytes hash obs)=
       VerifyPrefix.verify (FinishModel.finish R B) D pub bytes hash obs := by
```

```diff
### S1SemanticCodeVerifyV1 -> RPz7_S1SemanticCodeVerifyV1
--- evidence/sdk-child2-20261026/SdkD_085/sources/S1SemanticCodeVerifyV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticCodeVerifyV1.lean
@@ -11,5 +11,5 @@
 abbrev Finish := {H : Type} → aspis_core.Digest32 H →
   pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix →
-  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (verifier.Phase → Result Unit) →
+  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (RPz7_PhaseIso.Phase → Result Unit) →
   Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
 
@@ -18,5 +18,5 @@
   (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
   (bytes : Slice Std.U8) (hash : H)
-  (obs : Option (verifier.Phase → Result Unit)) :
+  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
   Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
   := do
```

```diff
### S1SemanticFinishBoundsV1 -> RPz7_S1SemanticFinishBoundsV1
--- evidence/port17release-20261024/dependency-source/S1SemanticFinishBoundsV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticFinishBoundsV1.lean
@@ -27,5 +27,5 @@
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
     (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
-    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
     (h : FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)) :
     ∃ running t25 record25 record26 z0 t26 z1 t27,
```

```diff
### S1SemanticFinishModelV1 -> RPz7_S1SemanticFinishModelV1
--- evidence/port17release-20261024/dependency-source/S1SemanticFinishModelV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticFinishModelV1.lean
@@ -226,5 +226,5 @@
   (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
   (challenges : r1_wire.Challenges)
-  (obs : Option (verifier.Phase → Result Unit)) :
+  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
   Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
   := do
```

```diff
### S1SemanticFinishRootsV1 -> RPz7_S1SemanticFinishRootsV1
--- evidence/port17release-20261024/dependency-source/S1SemanticFinishRootsV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticFinishRootsV1.lean
@@ -29,5 +29,5 @@
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
     (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
-    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
+    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
     (h : FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)) :
     ∃ (rootPayload : Slice U8)
```

```diff
### S1SemanticPhaseV1 -> RPz7_S1SemanticPhaseV1
--- evidence/port17release-20261024/dependency-source/S1SemanticPhaseV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticPhaseV1.lean
@@ -1,10 +1,6 @@
-import CurrentCompactFirstCompositionV1
+import RPz7_PhaseIso
 set_option autoImplicit false
-namespace AspisR1PublicPreparation.verifier
-/-- The full retained caller phase carrier, with every variant and payload.
-This naming alias supplies the nominal phase absent from the selected legacy
-public-preparation cache. Source-body transports below use release None. -/
-abbrev Phase := AspisR1PublicPreparation.FirstCaller.Phase
-end AspisR1PublicPreparation.verifier
-
-#print axioms AspisR1PublicPreparation.verifier.Phase
+/-! Lead-owned S1 phase replacement. The original has no theorems: its only
+export is the conflicting abbreviation. The retained S1 carrier now lives in
+RPz7_PhaseIso.Phase, with explicit producer/callback/consumer transports. -/
+#print axioms RPz7_PhaseIso.Phase
```

```diff
### S1SemanticPrefixModelV1 -> RPz7_S1SemanticPrefixModelV1
--- evidence/port17release-20261024/dependency-source/S1SemanticPrefixModelV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticPrefixModelV1.lean
@@ -6,8 +6,8 @@
 abbrev VerifyPrefix.Finish := {H : Type} → aspis_core.Digest32 H →
   pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix →
-  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (verifier.Phase → Result Unit) →
+  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (RPz7_PhaseIso.Phase → Result Unit) →
   Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
 def VerifyPrefix.mark
-  (obs : Option (verifier.Phase → Result Unit)) (i : Std.U8) :
+  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (i : Std.U8) :
   Result Unit
   := do
@@ -18,5 +18,5 @@
   (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
   (bytes : Slice Std.U8) (hash : H)
-  (obs : Option (verifier.Phase → Result Unit)) :
+  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
   Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
   := do
```

```diff
### S1SemanticVerifyReachabilityV1 -> RPz7_S1SemanticVerifyReachabilityV1
--- evidence/port17release-20261024/dependency-source/S1SemanticVerifyReachabilityV1.lean
+++ evidence/replay-dry8-20261026/RPz7_S1SemanticVerifyReachabilityV1.lean
@@ -25,5 +25,5 @@
 theorem verify_success (F : Finish) {H : Type} (D : aspis_core.Digest32 H)
     (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
-    (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
+    (bytes : Slice U8) (hash : H) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
     (out : r1_semantic.Verified H)
     (h : verify F D pub bytes hash obs = ok (.Ok out)) :
```
