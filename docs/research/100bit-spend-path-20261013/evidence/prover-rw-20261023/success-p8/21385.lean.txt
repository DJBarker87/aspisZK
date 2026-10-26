import R1Z.PV_ArrayReadValue
import R1Z.PV_CompressArity
import R1Z.PV_CompressInstalledTotal
import R1Z.PV_CompressLastPower
import R1Z.PV_CompressList
import R1Z.PV_CompressModel
import R1Z.PV_CompressModelTotal
import R1Z.PV_CompressSuffix
import R1Z.PV_CompressTransport
import R1Z.PV_CurrentBody
import R1Z.PV_CurrentDictionary
import R1Z.PV_CurrentQuarticBridge
import R1Z.PV_CurrentQuarticTotal
import R1Z.PV_CurrentScale
import R1Z.PV_CurrentScaleBody
import R1Z.PV_CurrentScaleInstall
import R1Z.PV_CurrentSquare
import R1Z.PV_DictionaryUpdate
import R1Z.PV_OrdinaryByteBridge
import R1Z.PV_OrdinaryDecodeBridge
import R1Z.PV_OrdinaryDigitsBridge
import R1Z.PV_OrdinaryDivBridge
import R1Z.PV_OrdinaryNormalize
import R1Z.PV_OrdinaryPolicyBridge
import R1Z.PV_OrdinaryReferenceBody
import R1Z.PV_OrdinaryReferenceDictionary
import R1Z.PV_OrdinaryReferenceRank
import R1Z.PV_OrdinarySource
import R1Z.PV_PoleFold
import R1Z.PV_PoleLeafCorrect
import R1Z.PV_PoleLeafSource
import R1Z.PV_PoleLeafValue
import R1Z.PV_PoleList
import R1Z.PV_ProverRwP7BodyCoefficients
import R1Z.PV_ProverRwP7CoefficientsInstall
import R1Z.PV_ProverRwP7CoefficientsSource
import R1Z.PV_ProverRwP7CurrentComplexBridge
import R1Z.PV_SamplerUpdate
import R1Z.PV_ScaleUpdate
import R1Z.PV_TraceValueBody
import R1Z.PV_TraceValueInstall
import R1Z.PV_TraceValueSource
import R1Z.PV_WordZero
import R1Z.PrivacyR1HeadlineDeployedReal

-- Focused cached audit, not a frozen release replay. Four local Std-only checks
-- retain their individual source/compiler/axiom receipts separately.
#print axioms R1Z.PV_ArrayReadValue.first
#print axioms R1Z.PV_ArrayReadValue.read
#print axioms R1Z.PV_ArrayReadValue.second
#print axioms R1Z.PV_CompressArity.length
#print axioms R1Z.PV_CompressArity.restriction
#print axioms R1Z.PV_CompressArity.values_length
#print axioms R1Z.PV_CompressInstalledTotal.fold
#print axioms R1Z.PV_CompressInstalledTotal.stateFold
#print axioms R1Z.PV_CompressLastPower.empty
#print axioms R1Z.PV_CompressLastPower.erase
#print axioms R1Z.PV_CompressLastPower.mul_total
#print axioms R1Z.PV_CompressLastPower.singleton
#print axioms R1Z.PV_CompressList.append
#print axioms R1Z.PV_CompressList.cons
#print axioms R1Z.PV_CompressList.nil
#print axioms R1Z.PV_CompressModel.compress
#print axioms R1Z.PV_CompressModel.loop
#print axioms R1Z.PV_CompressModelTotal.stateFold
#print axioms R1Z.PV_CompressSuffix.finite
#print axioms R1Z.PV_CompressSuffix.read
#print axioms R1Z.PV_CompressSuffix.step
#print axioms R1Z.PV_CompressTransport.fold
#print axioms R1Z.PV_CompressTransport.stateFold
#print axioms R1Z.PV_CurrentBody.caller
#print axioms R1Z.PV_CurrentDictionary.add_source
#print axioms R1Z.PV_CurrentDictionary.dictionary_preserved
#print axioms R1Z.PV_CurrentDictionary.mul_source
#print axioms R1Z.PV_CurrentQuarticBridge.add
#print axioms R1Z.PV_CurrentQuarticBridge.mul
#print axioms R1Z.PV_CurrentQuarticBridge.mul_by_r
#print axioms R1Z.PV_CurrentQuarticTotal.complex_add
#print axioms R1Z.PV_CurrentQuarticTotal.complex_mul
#print axioms R1Z.PV_CurrentQuarticTotal.mul_by_r
#print axioms R1Z.PV_CurrentQuarticTotal.square
#print axioms R1Z.PV_CurrentScale.complex
#print axioms R1Z.PV_CurrentScale.quartic
#print axioms R1Z.PV_CurrentScaleBody.caller
#print axioms R1Z.PV_CurrentScaleInstall.dictionary_preserved
#print axioms R1Z.PV_CurrentScaleInstall.source
#print axioms R1Z.PV_CurrentSquare.complex
#print axioms R1Z.PV_CurrentSquare.total
#print axioms R1Z.PV_DictionaryUpdate.preserve
#print axioms R1Z.PV_OrdinaryByteBridge.body
#print axioms R1Z.PV_OrdinaryByteBridge.loop
#print axioms R1Z.PV_OrdinaryDecodeBridge.decode
#print axioms R1Z.PV_OrdinaryDecodeBridge.decode_success
#print axioms R1Z.PV_OrdinaryDecodeBridge.ordinary
#print axioms R1Z.PV_OrdinaryDigitsBridge.body
#print axioms R1Z.PV_OrdinaryDigitsBridge.digits
#print axioms R1Z.PV_OrdinaryDigitsBridge.loop
#print axioms R1Z.PV_OrdinaryDivBridge.body
#print axioms R1Z.PV_OrdinaryDivBridge.loop
#print axioms R1Z.PV_OrdinaryDivBridge.pass
#print axioms R1Z.PV_OrdinaryDivBridge.zero
#print axioms R1Z.PV_OrdinaryNormalize.construct
#print axioms R1Z.PV_OrdinaryNormalize.current
#print axioms R1Z.PV_OrdinaryNormalize.fromW_injective
#print axioms R1Z.PV_OrdinaryNormalize.old
#print axioms R1Z.PV_OrdinaryNormalize.roundtrip
#print axioms R1Z.PV_OrdinaryPolicyBridge.policy
#print axioms R1Z.PV_OrdinaryPolicyBridge.reference
#print axioms R1Z.PV_OrdinaryReferenceBody.caller
#print axioms R1Z.PV_OrdinaryReferenceDictionary.dictionaries
#print axioms R1Z.PV_OrdinaryReferenceRank.rank
#print axioms R1Z.PV_OrdinarySource.bytes_done
#print axioms R1Z.PV_OrdinarySource.digits_done
#print axioms R1Z.PV_OrdinarySource.ordinary_unfold
#print axioms R1Z.PV_PoleFold.absorbing
#print axioms R1Z.PV_PoleFold.inactive
#print axioms R1Z.PV_PoleFold.row_value
#print axioms R1Z.PV_PoleFold.total
#print axioms R1Z.PV_PoleLeafCorrect.absorbing
#print axioms R1Z.PV_PoleLeafCorrect.equal
#print axioms R1Z.PV_PoleLeafCorrect.inactive
#print axioms R1Z.PV_PoleLeafCorrect.keep_clear
#print axioms R1Z.PV_PoleLeafSource.equal_total
#print axioms R1Z.PV_PoleLeafValue.same_words
#print axioms R1Z.PV_PoleLeafValue.source
#print axioms R1Z.PV_PoleLeafValue.source_comm
#print axioms R1Z.PV_PoleLeafValue.source_self
#print axioms R1Z.PV_PoleLeafValue.zero
#print axioms R1Z.PV_PoleLeafValue.zero_symmetric
#print axioms R1Z.PV_PoleList.append
#print axioms R1Z.PV_PoleList.total
#print axioms R1Z.PV_PoleList.value
#print axioms R1Z.PV_ProverRwP7BodyCoefficients.caller
#print axioms R1Z.PV_ProverRwP7BodyCoefficients.continuation
#print axioms R1Z.PV_ProverRwP7CoefficientsInstall.callback_removed
#print axioms R1Z.PV_ProverRwP7CoefficientsInstall.clone_preserved
#print axioms R1Z.PV_ProverRwP7CoefficientsInstall.fibre_preserved
#print axioms R1Z.PV_ProverRwP7CoefficientsInstall.source
#print axioms R1Z.PV_ProverRwP7CoefficientsSource.coefficients_unfold
#print axioms R1Z.PV_ProverRwP7CurrentComplexBridge.add
#print axioms R1Z.PV_ProverRwP7CurrentComplexBridge.double
#print axioms R1Z.PV_ProverRwP7CurrentComplexBridge.mul
#print axioms R1Z.PV_ProverRwP7CurrentComplexBridge.sub
#print axioms R1Z.PV_SamplerUpdate.preserve
#print axioms R1Z.PV_ScaleUpdate.preserve
#print axioms R1Z.PV_TraceValueBody.caller
#print axioms R1Z.PV_TraceValueBody.continuation
#print axioms R1Z.PV_TraceValueInstall.callback_removed
#print axioms R1Z.PV_TraceValueInstall.clone_preserved
#print axioms R1Z.PV_TraceValueInstall.source
#print axioms R1Z.PV_TraceValueSource.exact
#print axioms R1Z.PV_TraceValueSource.operands_erased
#print axioms R1Z.PV_WordZero.four_or_zero
#print axioms R1Z.PV_WordZero.or_zero
#print axioms R1Z.PV_WordZero.xor_self
#print axioms R1Z.PV_WordZero.xor_zero
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
