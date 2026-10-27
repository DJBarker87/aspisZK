-- One final audit of the callback/helper closure and resumed proofs.
-- This is not the deployed privacy endpoint replay.
import R1Z.PV_CB3_Afterstate
import R1Z.PV_CB3_Op246Coherent
import R1Z.PV_CB3_TransitionExtracted
import R1Z.PV_CB3_Op225Coherent
import R1Z.PV_CB3_Op229Source
import R1Z.PV_CB3_Op51Source
import R1Z.PV_CB3_Op120Source
import R1Z.PV_CB3_CallbackBundle
import R1Z.PV_CB3_SamplerCarry
import R1Z.PV_CB3_DigitBlocks
import R1Z.PV_CB3_DigitInjective
import R1Z.PV_CB3_SamplerDivision
import R1Z.PV_CB3_DigitSequence
import R1Z.PV_CB3_RankBound
import R1Z.PV_CB3_GammaWrap
import R1Z.PV_CB3_GammaDigits
import R1Z.PV_CB3_GammaRank
import R1Z.PV_CB3_SamplerWord
import R1Z.PV_CB3_GammaBounds
import R1Z.PV_CB3_GammaBytes
import R1Z.PV_CB3_GammaExact
import R1Z.PV_CB3_ListLoops
import R1Z.PV_CB3_WordBits
import R1Z.PV_CB3_WordMachine
import R1Z.PV_CB3_MachineCarryStep
import R1Z.PV_CB3_MachineCarry
import R1Z.PV_CB3_MachinePass
import R1Z.PV_CB3_MachineDigits
import R1Z.PV_CB3_MachineFinish
import R1Z.PV_CB3_QuotientHead
import R1Z.PV_CB3_MachineHigh
import R1Z.PV_CB3_MachineGamma
import R1Z.PV_CB3_MonadicLoops
import R1Z.PV_CB3_PoleRows
import R1Z.PV_CB3_SamplerWordSource
import R1Z.PV_CB3_WordArithmetic
import R1Z.PV_CB3_SourcePass
import R1Z.PV_CB3_SourceABI
import R1Z.PV_CB3_SourceShape
import R1Z.PV_CB3_ArrayEight
import R1Z.PV_CB3_ByteTotal
import R1Z.PV_CB3_Op51Arbitrary
import R1Z.PV_CB3_StagedByteBits
import R1Z.PV_CB3_StagedByteShape
import R1Z.PV_CB3_StagedByteWord
import R1Z.PV_CB3_StagedCast
import R1Z.PV_CB3_StagedComposition
import R1Z.PV_CB3_StagedDecode
import R1Z.PV_CB3_StagedFields
import R1Z.PV_CB3_StagedFinish
import R1Z.PV_CB3_StagedGammaTotal
import R1Z.PV_CB3_StagedIndex
import R1Z.PV_CB3_StagedKernel
import R1Z.PV_CB3_StagedLoadInspect
import R1Z.PV_CB3_StagedMachineCarry
import R1Z.PV_CB3_StagedMachinePass
import R1Z.PV_CB3_StagedMachineStep
import R1Z.PV_CB3_StagedNativeLink
import R1Z.PV_CB3_StagedNormalize
import R1Z.PV_CB3_StagedPacking
import R1Z.PV_CB3_StagedPair
import R1Z.PV_CB3_StagedPass
import R1Z.PV_CB3_StagedScalarInspect
import R1Z.PV_CB3_StagedSource
import R1Z.PV_CB3_StagedSplit
import R1Z.PV_CB3_StagedTotal
import R1Z.PV_CB3_StagedWord
import R1Z.PV_CB3_StagedZero

#print axioms R1Z.PV_CB3_CallbackBundle.op51_source
#print axioms R1Z.PV_CB3_CallbackBundle.op120_source
#print axioms R1Z.PV_CB3_CallbackBundle.op225_source
#print axioms R1Z.PV_CB3_CallbackBundle.op229_source
#print axioms R1Z.PV_CB3_CallbackBundle.op246_source
#print axioms R1Z.PV_CB3_ArrayEight.view
#print axioms R1Z.PV_CB3_ByteTotal.total
#print axioms R1Z.PV_CB3_Op51Arbitrary.carrier_complete
#print axioms R1Z.PV_CB3_Op51Arbitrary.op51_source
#print axioms R1Z.PV_CB3_StagedByteBits.shift_value
#print axioms R1Z.PV_CB3_StagedByteBits.or_low
#print axioms R1Z.PV_CB3_StagedByteShape.source
#print axioms R1Z.PV_CB3_StagedByteWord.value
#print axioms R1Z.PV_CB3_StagedCast.narrow
#print axioms R1Z.PV_CB3_StagedComposition.bind_total
#print axioms R1Z.PV_CB3_StagedComposition.read_total
#print axioms R1Z.PV_CB3_StagedComposition.words_total
#print axioms R1Z.PV_CB3_StagedComposition.pass_total
#print axioms R1Z.PV_CB3_StagedDecode.suffix_eq
#print axioms R1Z.PV_CB3_StagedDecode.total
#print axioms R1Z.PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new
#print axioms R1Z.PV_CB3_StagedFinish.carry_bits
#print axioms R1Z.PV_CB3_StagedFinish.neq_zero
#print axioms R1Z.PV_CB3_StagedFinish.overflow
#print axioms R1Z.PV_CB3_StagedFinish.increment
#print axioms R1Z.PV_CB3_StagedFinish.projection
#print axioms R1Z.PV_CB3_StagedGammaTotal.carry_total
#print axioms R1Z.PV_CB3_StagedGammaTotal.gamma_total
#print axioms R1Z.PV_CB3_StagedIndex.read0
#print axioms R1Z.PV_CB3_StagedIndex.read1
#print axioms R1Z.PV_CB3_StagedIndex.read2
#print axioms R1Z.PV_CB3_StagedIndex.read3
#print axioms R1Z.PV_CB3_StagedIndex.read4
#print axioms R1Z.PV_CB3_StagedIndex.read5
#print axioms R1Z.PV_CB3_StagedIndex.read6
#print axioms R1Z.PV_CB3_StagedIndex.read7
#print axioms R1Z.PV_CB3_StagedKernel.source
#print axioms R1Z.PV_CB3_StagedLoadInspect.byte_bound
#print axioms R1Z.PV_CB3_StagedMachineCarry.source
#print axioms R1Z.PV_CB3_StagedMachinePass.source
#print axioms R1Z.PV_CB3_StagedMachineStep.word
#print axioms R1Z.PV_CB3_StagedMachineStep.carry
#print axioms R1Z.PV_CB3_StagedMachineStep.shift_literal
#print axioms R1Z.PV_CB3_StagedNativeLink.constant
#print axioms R1Z.PV_CB3_StagedNativeLink.subtract
#print axioms R1Z.PV_CB3_StagedNativeLink.reduce
#print axioms R1Z.PV_CB3_StagedNativeLink.word
#print axioms R1Z.PV_CB3_StagedNativeLink.canonical
#print axioms R1Z.PV_CB3_StagedNativeLink.construct
#print axioms R1Z.PV_CB3_StagedNormalize.source
#print axioms R1Z.PV_CB3_StagedNormalize.constructor
#print axioms R1Z.PV_CB3_StagedNormalize.word_fixed
#print axioms R1Z.PV_CB3_StagedNormalize.fixed
#print axioms R1Z.PV_CB3_StagedNormalize.constructor_fixed
#print axioms R1Z.ProverRwSuccessNativeNormalize.native
#print axioms R1Z.PV_CB3_StagedPacking.word_eta
#print axioms R1Z.PV_CB3_StagedPacking.bits_length
#print axioms R1Z.PV_CB3_StagedPacking.bits_pack
#print axioms R1Z.PV_CB3_StagedPacking.pack_bits
#print axioms R1Z.PV_CB3_StagedPair.eliminate
#print axioms R1Z.PV_CB3_StagedPass.compose
#print axioms R1Z.PV_CB3_StagedPass.spec
#print axioms R1Z.PV_CB3_StagedSource.staged_reference.words
#print axioms R1Z.PV_CB3_StagedSource.staged_reference.word_step
#print axioms R1Z.PV_CB3_StagedSource.staged_reference.pass
#print axioms R1Z.PV_CB3_StagedSource.staged_reference.carry_step
#print axioms R1Z.PV_CB3_StagedSource.staged_reference.carry
#print axioms R1Z.PV_CB3_StagedSource.staged_reference.gamma
#print axioms R1Z.PV_CB3_StagedSplit.pass_words
#print axioms R1Z.PV_CB3_StagedSplit.pass_digit
#print axioms R1Z.PV_CB3_StagedSplit.projection
#print axioms R1Z.PV_CB3_StagedSplit.length
#print axioms R1Z.PV_CB3_StagedTotal.constructor_total
#print axioms R1Z.PV_CB3_StagedTotal.read_eq
#print axioms R1Z.PV_CB3_StagedWord.word_eq
#print axioms R1Z.PV_CB3_StagedWord.word_total
#print axioms R1Z.PV_CB3_StagedWord.carry_total
#print axioms R1Z.PV_CB3_StagedZero.neq_zero
