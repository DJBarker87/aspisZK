import FIr_AcceptedTerminal
import FIr_AlphaCanonical
import FIr_AlphaLiteral
import FIr_AlphaTerminal
import FIr_ArrayRead
import FIr_BuilderCanonical
import FIr_CarrierCanonical
import FIr_Chain
import FIr_ChainNonvacuity
import FIr_ChainTop
import FIr_ChallengeValue
import FIr_CompositionColumns
import FIr_CompositionH1
import FIr_EntryIndex
import FIr_EqualityCell
import FIr_EqualityLoop
import FIr_EqualityProduct
import FIr_EqualityReach
import FIr_EqualityShape
import FIr_EqualityValue
import FIr_FinalInstall
import FIr_FinishComparison
import FIr_GCanonical
import FIr_GatherCallback
import FIr_GatherCanonical
import FIr_GlobalOwners
import FIr_GlobalOwners2
import FIr_H1Canonical
import FIr_LastLiteral
import FIr_LastMasked
import FIr_LiteralRow
import FIr_LiteralValues
import FIr_MaskedArithmetic
import FIr_NativeArithmetic
import FIr_NativeArray
import FIr_NativeCM
import FIr_NativeQM
import FIr_NativeScalar
import FIr_NativeSub
import FIr_NativeValue
import FIr_Nonvacuity
import FIr_OwnerEquivalence
import FIr_PhysicalChain
import FIr_PhysicalInitial
import FIr_PublicProjection
import FIr_RootRefined
import FIr_RootValue
import FIr_SampleRange
import FIr_SelectedClaim
import FIr_SourceChain
import FIr_SourceInitial
import FIr_SourceLast
import FIr_TerminalPartsValue
import FIr_TerminalTrace
import FIr_TerminalValue
import FIr_Top
import FIr_TranscriptRange
import FIr_Weaker
import FIr_FinalStatements
#print axioms AspisR1.FIr_AcceptedTerminal.verified
#print axioms AspisR1.FIr_AlphaCanonical.entry
#print axioms AspisR1.FIr_AlphaCanonical.alpha
#print axioms AspisR1.FIr_AlphaCanonical.verified
#print axioms AspisR1.FIr_AlphaLiteral.value
#print axioms AspisR1.FIr_AlphaTerminal.reached
#print axioms AspisR1.FIr_ArrayRead.slot
#print axioms AspisR1.FIr_ArrayRead.member
#print axioms AspisR1.FIr_BuilderCanonical.loop
#print axioms AspisR1.FIr_BuilderCanonical.fromFn
#print axioms AspisR1.FIr_CarrierCanonical.to_canon
#print axioms AspisR1.FIr_CarrierCanonical.to_value
#print axioms AspisR1.FIr_CarrierCanonical.from_canon
#print axioms AspisR1.FIr_CarrierCanonical.from_value
#print axioms AspisR1.FIr_CarrierCanonical.array
#print axioms AspisR1.FIr_CarrierCanonical.claims
#print axioms AspisR1.FIr_Chain.adjacent
#print axioms AspisR1.FIr_Chain.last_value
#print axioms AspisR1.FIr_ChainNonvacuity.composed
#print axioms AspisR1.FIr_ChainTop.deployed
#print axioms AspisR1.FIr_ChallengeValue.decode_value
#print axioms AspisR1.FIr_ChallengeValue.alpha_same
#print axioms AspisR1.FIr_CompositionColumns.reached
#print axioms AspisR1.FIr_CompositionH1.reached
#print axioms AspisR1.FIr_EntryIndex.length
#print axioms AspisR1.FIr_EntryIndex.round
#print axioms AspisR1.FIr_EntryIndex.challenge
#print axioms AspisR1.FIr_EqualityCell.value
#print axioms AspisR1.FIr_EqualityLoop.exact_loop
#print axioms AspisR1.FIr_EqualityProduct.product
#print axioms AspisR1.FIr_EqualityProduct.model
#print axioms AspisR1.FIr_EqualityReach.reached
#print axioms AspisR1.FIr_EqualityShape.step
#print axioms AspisR1.FIr_EqualityValue.exact_value
#print axioms AspisR1.FIr_FinalInstall.unchanged
#print axioms AspisR1.FIr_FinalInstall.terminal_fixed
#print axioms AspisR1PublicPreparation.FIr_FinishComparison.qm_eq_source
#print axioms AspisR1PublicPreparation.FIr_FinishComparison.qm_ne_false_eq
#print axioms AspisR1PublicPreparation.FIr_FinishComparison.terminal_comparison_of_finish_success
#print axioms AspisR1.FIr_GCanonical.canonical
#print axioms AspisR1.FIr_GatherCallback.selected
#print axioms AspisR1.FIr_GatherCanonical.gathered
#print axioms AspisR1.FIr_GlobalOwners.complete
#print axioms AspisR1.FIr_GlobalOwners2.complete
#print axioms AspisR1.FIr_H1Canonical.canonical
#print axioms AspisR1.FIr_LastLiteral.value
#print axioms AspisR1.FIr_LastMasked.value
#print axioms AspisR1.FIr_LiteralRow.decode_row
#print axioms AspisR1.FIr_LiteralRow.parsed_row
#print axioms AspisR1.FIr_LiteralValues.claim
#print axioms AspisR1.FIr_LiteralValues.polynomials
#print axioms AspisR1.FIr_MaskedArithmetic.value
#print axioms AspisR1.FIr_NativeArithmetic.bind_map
#print axioms AspisR1.FIr_NativeArithmetic.m31_add
#print axioms AspisR1.FIr_NativeArithmetic.m31_sub
#print axioms AspisR1.FIr_NativeArithmetic.m31_reduce
#print axioms AspisR1.FIr_NativeArithmetic.m31_mul
#print axioms AspisR1.FIr_NativeArray.slot
#print axioms AspisR1.FIr_NativeArray.read
#print axioms AspisR1.FIr_NativeArray.canonical
#print axioms AspisR1.FIr_NativeCM.add
#print axioms AspisR1.FIr_NativeCM.sub
#print axioms AspisR1.FIr_NativeCM.mul
#print axioms AspisR1.FIr_NativeCM.by_r
#print axioms AspisR1.FIr_NativeQM.add
#print axioms AspisR1.FIr_NativeQM.mul
#print axioms AspisR1.FIr_NativeScalar.sub_same
#print axioms AspisR1.FIr_NativeScalar.sub
#print axioms AspisR1.FIr_NativeSub.cm
#print axioms AspisR1.FIr_NativeSub.qm
#print axioms AspisR1.FIr_NativeValue.add
#print axioms AspisR1.FIr_NativeValue.mul
#print axioms AspisR1.FIr_NativeValue.zero
#print axioms AspisR1.FIr_NativeValue.one
#print axioms AspisR1.FIr_Nonvacuity.composed
#print axioms AspisR1.FIr_OwnerEquivalence.project
#print axioms AspisR1.FIr_OwnerEquivalence.equivalent
#print axioms AspisR1.FIr_PhysicalChain.on_run
#print axioms AspisR1.FIr_PhysicalInitial.parsed_rows
#print axioms AspisR1.FIr_PhysicalInitial.on_run
#print axioms AspisR1.FIr_PublicProjection.transfer
#print axioms AspisR1.FIr_PublicProjection.withdrawal
#print axioms AspisR1.FIr_RootRefined.parts
#print axioms AspisR1.FIr_RootValue.reached
#print axioms AspisR1.FIr_SampleRange.zero
#print axioms AspisR1.FIr_SampleRange.sigma
#print axioms AspisR1.FIr_SampleRange.sampled
#print axioms AspisR1.FIr_SelectedClaim.reached
#print axioms AspisR1.FIr_SelectedClaim.canonical
#print axioms AspisR1.FIr_SourceChain.polynomial
#print axioms AspisR1.FIr_SourceChain.adjacent
#print axioms AspisR1.FIr_SourceInitial.head_state
#print axioms AspisR1.FIr_SourceInitial.first_boundary
#print axioms AspisR1.FIr_SourceLast.last_value
#print axioms AspisR1.FIr_TerminalPartsValue.reached_value
#print axioms AspisR1.FIr_TerminalTrace.reached
#print axioms AspisR1.FIr_TerminalValue.arithmetic
#print axioms AspisR1.FIr_Top.deployed
#print axioms AspisR1.FIr_TranscriptRange.program
#print axioms AspisR1.FIr_TranscriptRange.getD
#print axioms AspisR1.FIr_TranscriptRange.view
#print axioms AspisR1.FIr_GlobalOwners.of_original
#print axioms FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31

#check @AspisR1.FIr_AlphaTerminal.reached
#check @AspisR1.FIr_RootRefined.parts
#check @AspisR1.FIr_RootValue.reached
#check @AspisR1.FIr_GCanonical.canonical
#check @AspisR1.FIr_LastLiteral.value
#check @AspisR1.FIr_LastMasked.value

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "_private.FIr_FinishComparison." then
      elabCommand (← `(#print axioms $(mkIdent name)))
#check @AspisR1.FIr_Top.deployed
#check @AspisR1.FIr_Nonvacuity.composed
