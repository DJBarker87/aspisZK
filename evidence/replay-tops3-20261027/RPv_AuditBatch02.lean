import Lean
import RPv_SelectedClaimGatherSlice
import RPv_Qm31PackBase4Slice
import RPv_Qm31PackBase4SliceFacts
import RPv_ExtractedMaskQmPackBase4Array
import RPv_ExtractedMaskQmPackBase4InitCopy
import RPv_ExtractedMaskQmPackBase4Arithmetic
import RPv_ExtractedMaskQmPackBase4SourceArithmetic
import RPv_ExtractedMaskQmPackBase4CheckedU64
import RPv_ExtractedMaskQmPackBase4Tail
import RPv_ExtractedMaskQmPackBase4Fragments
import RPv_ExtractedMaskQmPackBase4Whole
import RPv_FIw_PackArithmetic
import RPv_FIw_PackValue
import RPv_FIw_PackSource
import RPv_FIx_PreweightedPack
import RPv_FIx_PreweightedGroup
import RPv_FIx_PreweightedLoopStep
import RPv_FIx_PreweightedLoop
import RPv_FIx_WordArithmetic
import RPv_FIx_Preweighted
import RPv_FIx_PreweightedModel
import RPv_FIx_PreweightedPointwise
import RPv_FIx_SelectedMeaning
import RPv_FIy_DigestLane
import RPv_FIy_DigestLoopStep
import RPv_FIy_DigestLoop
import RPv_FIy_DigestClosed
import RPv_FIy_DigestBinding
import RPv_FIw_SelectorRow
import RPv_FIy_FrontierStep
import RPv_FIy_FrontierLoopStep
import RPv_FIy_EmptyRootShape
import RPv_FIy_EmptyRootMap
import RPv_FIy_EmptyRootBounds
import RPv_FIy_EmptyRoot
import RPv_FIy_FrontierMeaning
import RPv_FIy_ValueSelector
import RPv_FIy_ValueShifts
import RPv_FIx_ReconstructStep
import RPv_FIx_ReconstructTraversal
import RPv_FIx_ReconstructFold
import RPv_FIx_ReconstructSource
import RPv_FIx_ReconstructSlice
import RPv_FIx_ReconstructSliceValue
import RPv_FIx_ReconstructValue
import RPv_SelectorReconstructIndexModel
import RPv_FIx_ReconstructPrefixModel
import RPv_FIx_ReconstructMeaning
import RPv_FIy_ValueTail
import RPv_FIx_ValueConservation
import RPv_FIx_SquareMap
import RPv_FIx_SquareValue
import RPv_FIx_ValueBitModel
import RPv_FIx_ValueIndices
import RPv_FIx_ValueBits0
import RPv_FIx_ValueBits1
import RPv_FIx_ValueBits2
import RPv_FIx_ValueBitClosed
import RPv_FIx_ValueBitPrefix
import RPv_FIx_ValueConservationSource
import RPv_FIx_ConservationMeaning
import RPv_FIy_IteratorTraversal
import RPv_FIy_Writeback
import RPv_FIy_WritebackCells
import RPv_FIy_IteratorCanonical
import RPv_FIy_ScaleReadback
import RPv_FIy_Scaling
import RPv_FIx_PreweightedMeaning
import RPv_FIy_ValuePacked
import RPv_FIx_PathIndices
import RPv_FIx_PathStep
import RPv_FIx_PathLoopStep
import RPv_FIx_PathAlgebra
import RPv_FIx_PathLoop
import RPv_FIy_OccupancyStep
import RPv_FIy_OccupancyLoopStep
import RPv_FIy_OccupancyLoop
import RPv_FIy_OccupancyPrefix
import RPv_FIy_OccupancyTail
import RPv_FIy_OccupancySource
import RPv_FIy_OccupancyClosed
import RPv_FIy_OccupancyMeaning
import RPv_FIy_OccupancyRows
import RPv_FIy_OccupancyModel
import RPv_FIy_OccupancyList
import RPv_FIy_OccupancyPacked
import RPv_FIy_FrontierFrame
import RPv_FIy_FrontierLoop
import RPv_FIy_Frontier20
import RPv_FIy_PublicDigestStep
import RPv_FIy_PublicDigestPrefix
import RPv_FIy_PublicDigestSuffix
import RPv_FIy_PublicDigestSource
import RPv_FIy_PublicDigest
import RPv_FIw_ScalarIndices
import RPv_FIw_CoefficientMeaning
import RPv_FIw_CoefficientTransport
import RPv_FIw_ScalarSuffix
import RPv_FIx_Absorption
import RPv_FIx_InitialVariant
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_SelectedClaimGatherSlice, `RPv_Qm31PackBase4Slice, `RPv_Qm31PackBase4SliceFacts, `RPv_ExtractedMaskQmPackBase4Array, `RPv_ExtractedMaskQmPackBase4InitCopy, `RPv_ExtractedMaskQmPackBase4Arithmetic, `RPv_ExtractedMaskQmPackBase4SourceArithmetic, `RPv_ExtractedMaskQmPackBase4CheckedU64, `RPv_ExtractedMaskQmPackBase4Tail, `RPv_ExtractedMaskQmPackBase4Fragments, `RPv_ExtractedMaskQmPackBase4Whole, `RPv_FIw_PackArithmetic, `RPv_FIw_PackValue, `RPv_FIw_PackSource, `RPv_FIx_PreweightedPack, `RPv_FIx_PreweightedGroup, `RPv_FIx_PreweightedLoopStep, `RPv_FIx_PreweightedLoop, `RPv_FIx_WordArithmetic, `RPv_FIx_Preweighted, `RPv_FIx_PreweightedModel, `RPv_FIx_PreweightedPointwise, `RPv_FIx_SelectedMeaning, `RPv_FIy_DigestLane, `RPv_FIy_DigestLoopStep, `RPv_FIy_DigestLoop, `RPv_FIy_DigestClosed, `RPv_FIy_DigestBinding, `RPv_FIw_SelectorRow, `RPv_FIy_FrontierStep, `RPv_FIy_FrontierLoopStep, `RPv_FIy_EmptyRootShape, `RPv_FIy_EmptyRootMap, `RPv_FIy_EmptyRootBounds, `RPv_FIy_EmptyRoot, `RPv_FIy_FrontierMeaning, `RPv_FIy_ValueSelector, `RPv_FIy_ValueShifts, `RPv_FIx_ReconstructStep, `RPv_FIx_ReconstructTraversal, `RPv_FIx_ReconstructFold, `RPv_FIx_ReconstructSource, `RPv_FIx_ReconstructSlice, `RPv_FIx_ReconstructSliceValue, `RPv_FIx_ReconstructValue, `RPv_SelectorReconstructIndexModel, `RPv_FIx_ReconstructPrefixModel, `RPv_FIx_ReconstructMeaning, `RPv_FIy_ValueTail, `RPv_FIx_ValueConservation, `RPv_FIx_SquareMap, `RPv_FIx_SquareValue, `RPv_FIx_ValueBitModel, `RPv_FIx_ValueIndices, `RPv_FIx_ValueBits0, `RPv_FIx_ValueBits1, `RPv_FIx_ValueBits2, `RPv_FIx_ValueBitClosed, `RPv_FIx_ValueBitPrefix, `RPv_FIx_ValueConservationSource, `RPv_FIx_ConservationMeaning, `RPv_FIy_IteratorTraversal, `RPv_FIy_Writeback, `RPv_FIy_WritebackCells, `RPv_FIy_IteratorCanonical, `RPv_FIy_ScaleReadback, `RPv_FIy_Scaling, `RPv_FIx_PreweightedMeaning, `RPv_FIy_ValuePacked, `RPv_FIx_PathIndices, `RPv_FIx_PathStep, `RPv_FIx_PathLoopStep, `RPv_FIx_PathAlgebra, `RPv_FIx_PathLoop, `RPv_FIy_OccupancyStep, `RPv_FIy_OccupancyLoopStep, `RPv_FIy_OccupancyLoop, `RPv_FIy_OccupancyPrefix, `RPv_FIy_OccupancyTail, `RPv_FIy_OccupancySource, `RPv_FIy_OccupancyClosed, `RPv_FIy_OccupancyMeaning, `RPv_FIy_OccupancyRows, `RPv_FIy_OccupancyModel, `RPv_FIy_OccupancyList, `RPv_FIy_OccupancyPacked, `RPv_FIy_FrontierFrame, `RPv_FIy_FrontierLoop, `RPv_FIy_Frontier20, `RPv_FIy_PublicDigestStep, `RPv_FIy_PublicDigestPrefix, `RPv_FIy_PublicDigestSuffix, `RPv_FIy_PublicDigestSource, `RPv_FIy_PublicDigest, `RPv_FIw_ScalarIndices, `RPv_FIw_CoefficientMeaning, `RPv_FIw_CoefficientTransport, `RPv_FIw_ScalarSuffix, `RPv_FIx_Absorption, `RPv_FIx_InitialVariant ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPV_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPV_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPV_AUDIT_COMPLETE declarations={count} modules={selected.size}"
