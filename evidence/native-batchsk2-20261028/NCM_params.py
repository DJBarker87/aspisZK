"""Own source generator: explicit unbundled NCE native bridge parameters."""
PARAMS = '''
    (keysZero : NCE_KeyProducerCuts.NCE_Native_KeysZero ops.keys.create)
    (keysWrite : NCE_KeyCuts.NCE_Native_KeysWrite ops.keys.write)
    (keysSort : NCE_SortCarrierCuts.NCE_Native_KeysSortCarrier ops.keys.sort)
    (valueSort : NCE_SortCuts.NCE_Native_KeysSort ops.valueSort)
    (get : NCE_KeyReadCuts.NCE_Native_KeysRead ops.leaf.get)
    (opening : NCE_OpeningCuts.NCE_Native_Opening ops.leaf.reader)
    (leafCut : NCE_LeafCuts.NCE_Native_Leaf ops.leaf.request ops.leaf.post)
    (countZero : NCE_CountInitCuts.NCE_Native_CountZero ops.count.create)
    (countCopy : NCE_CountInitCuts.NCE_Native_CountCopy ops.count.copy)
    (countScan : NCE_CountCuts.NCE_Native_CountScan ops.count.scan)
    (countStore : NCE_CountRowCuts.NCE_Native_CountCommit ops.count.store)
    (countHeight : NCE_CountLevelCuts.NCE_Native_CountHeight ops.count.height)
    (paddingCut : NCE_PaddingCuts.NCE_Native_Padding (NCM_PaddingPredicate.predicate base D) ops.padding)
    (row : NCE_CarrierEffects.NCE_Native_Row H ops.verifier.node)
    (rowStore : NCE_RowStoreCuts.NCE_Native_RowStore ops.rowStore)
    (verifier : NCE_VerifierCuts.NCE_Native_Verifier ops.verifier.entry ops.verifier.exit ops.verifier.finish)
    (admission : NCE_AdmissionCuts.NCE_Native_Admission ops.verifier.pair ops.verifier.range)
    (outer : NCE_OuterCuts.NCE_Native_ThreeTrees ops.start ops.after0 ops.after1 ops.finish)'''
ARGS='keysZero keysWrite keysSort valueSort get opening leafCut countZero countCopy countScan countStore countHeight paddingCut row rowStore verifier admission outer'
