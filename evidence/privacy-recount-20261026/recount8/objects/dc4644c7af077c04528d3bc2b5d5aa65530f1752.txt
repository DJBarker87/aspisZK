# Actual producer returns and exact remaining bank obligation

`PartsTail19.path_total/aux_total` (51192), `PartsTotal19.source/transfer/withdrawal` (51194) and `SourceBanks19.source/transfer/withdrawal` (51195) prove successful actual source Parts and CopyRecords.banks calls for both exact fixture record pairs. The two actual banks are defined by choosing those proved successful returns, not by substituting an arbitrary compiled Input. Their successful source equations have no new hypothesis. The general Parts/source-bank totality theorem requires the existing WitnessOk range facts; these are discharged by the inherited transfer_checked and withdrawal_checked facts for the concrete fixtures.

`BankMaterialized19.source/selected_eq` (51196) identifies actual stable/late columns from any successful Parts return. `BankGeometry19.stable/late` (51197) reduces the flat-array equality to pointwise source Parts cell equality. `SourceBankValidation19.source/transfer/withdrawal` (51198) then validates the **actual** source bank, conditionally on that cell equality. This cell hypothesis remains a P obligation; it has not been discharged or folded into T.

`PartsCells19.cells` (51200) identifies all path/auxiliary tail cells automatically from the actual Parts.path/aux arrays and reduces the remaining premise to exactly:

    ∀ b < 57, ∀ row < 16, ∀ lane < 16,
      (pt.blocks.val[b]!).val[row*16+lane]! =
        ((FixtureBanks19.certificate withdrawal b).row row).val[lane]!

This is the next producer identification obligation. The source already supplies `PV_Src_Forest_BlockCollect.parts_blocks` and `PV_Src_Forest_BlockResult.writer_ok`; use those with named writer/permutation results to prove each block equation, without reducing an entire bank. The certified target tables and their 57-block validation exist for both variants. Their equality to the actual successful source bank is still open.

The actual selected-i compiler-return equation is not established. The exact next downstream target remains `@PV_Src_NativeInput.run E_shipped shipped i = ok (.Ok i.compiled)` for the actual selected i. Full selected-i transition, deployed PublicBinding, and P∧hypotheticalT remain open in that order. No replacement selected Input was built. V152–V154 compile_call sub-obligations are reduced; whole V152–V154, V038, V045, V047 retained. Endpoint premise changes 0/0/0. Recount 5 is 407 rows: 400 P, 3 T, 4 C; OPEN 93.
