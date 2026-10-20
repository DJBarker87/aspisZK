import Lean
import R1RecordFrameCodec
import R1SemanticCoefficientCodec
import R1SemanticRecordCodec
import R0P.MaskView
import R1SemanticPayloadView
import R1SelectedSemanticPrefix
import R1SelectedSemanticPrefixFacts
import R1D18Transport
import R1LiteralTypedContext
import R1OutputCopyLinks
import R1OutputNotes
import R1AppendNode
import R1PairCopyLinks
import R1AppendPair
import R1InputPairCopyLinks
import R1InputPair
import R1SpendValues
import R1SpendSemantics
import R1InputPairSelection
import R1InputWitnessCore
import R1InputWitnessCheck
import R1AppendCopyLinks
import R1AppendPath
import SpendAppendBinding
import R1SpendAppendBinding
import SpendRelation
import R1SpendRelation
import R1SpendDataMap
import R1PublicBaseMap
import R1ExactBaseProjection

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1RecordFrameCodec, `R1SemanticCoefficientCodec, `R1SemanticRecordCodec, `R0P.MaskView, `R1SemanticPayloadView, `R1SelectedSemanticPrefix, `R1SelectedSemanticPrefixFacts, `R1D18Transport, `R1LiteralTypedContext, `R1OutputCopyLinks, `R1OutputNotes, `R1AppendNode, `R1PairCopyLinks, `R1AppendPair, `R1InputPairCopyLinks, `R1InputPair, `R1SpendValues, `R1SpendSemantics, `R1InputPairSelection, `R1InputWitnessCore, `R1InputWitnessCheck, `R1AppendCopyLinks, `R1AppendPath, `SpendAppendBinding, `R1SpendAppendBinding, `SpendRelation, `R1SpendRelation, `R1SpendDataMap, `R1PublicBaseMap, `R1ExactBaseProjection]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
