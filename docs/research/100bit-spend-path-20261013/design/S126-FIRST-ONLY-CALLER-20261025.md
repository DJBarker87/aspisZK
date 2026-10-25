# First-only enclosing S1/S6 consumers, 25 October 2026

Three checked theorems now need only the first-stage projection of the old
extraction boundary. Every previous conclusion is literally unchanged:

- `AspisS6SdkFirstOnly.original_sdk_reached_first` in S6SdkFirstOnlyV1.lean.
- `AspisS1SdkFirstOnlyPreparation.original_sdk_reached_preparation` in
  S1SdkFirstOnlyPreparationV1.lean.
- `AspisS1SdkFirstOnlyPhysical.original_sdk_physical_proof` in
  S1SdkFirstOnlyPhysicalV1.lean.

Before, each took native1, native2, hashv and the three-field
S2W_DigestExtraction.AeneasExtraction: stage1 equality, stage2 equality and
digestSource. After, each takes native1 and exactly this old first projection:

```
Stage1Extraction ops native1 :=
  ∀ program accounts data,
    native1 program accounts data =
      AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data
```

This is a genuine weakening from three source laws to their first projection,
not a structure bundling the old assumptions. `stage1_of_full` checks the
projection from the old boundary. There is no dummy second function or fabricated
second execution. The full cached original wrapper, complete SDK/account and
statement carriers, original accepted event, errors, effects and post-state
conclusions remain. The proof derives checkpoint/public framing directly from
original wrapper acceptance and the actual owned stage1 disjointness theorem.
It does not obtain framing through the old all-cuts/second-stage consumer.

The concrete first-stage equality is STILL A PREMISE. Library,
S2TrustedSdkBorrow, TrustedStd copy, Allocator and runtime entrypoint admission
remain. The S1 installed Ops/backend and all existing caller/math hypotheses
remain. No native SDK instance, std/allocator/runtime installation, event-log
transport or release binding has been established by this weakening. The
separate concrete digest/oracle binding remains necessary for the eventual
security theorem; the unchanged generic-digest conclusions here did not use
that extra source law. Its removal from these consumers is not a discharge
of the concrete oracle port elsewhere. Stage2 remains required for settlement.

Validation used only the three smallest changed targets, one at a time with
-j1 -M4400 and the atomic local lock; all passed on their first attempt.
S6:22.341425333s/RSS3871096832B; S1 preparation:3.410576375s/RSS3898703872B;
S1 physical:3.417528833s/RSS3912056832B. Swap0 throughout; all four #print axioms
reports contain only propext/Classical.choice/Quot.sound. One inherited unused
simp warning remains in the physical proof; it is not a failed check or an
excuse for an unchanged replay. Exact source/tool/import/command/revision pins
and source-only receipts are in the first-only packet. Its read-only audit
passes24pins and literal complete-conclusion comparisons for all three pairs.

This is an ACCEPTED-ONLY enclosing model/caller improvement under the displayed
source and SDK boundaries, not actual whole-source closure or R22 TOTAL.
S1/S6 and the <=2^-100 per-attempt release target remain NOT ESTABLISHED.
The ledger compiler-source freeze remains4bb3b3f51e16b4525f1d10336e2b0bcbbd775387;
no frozen production code, protocol, metric or deployment artifact changed.
