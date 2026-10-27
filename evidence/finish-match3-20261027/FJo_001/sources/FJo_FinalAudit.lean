import FJi_Grouped0
import FJi_Grouped1
import FJi_Grouped2
import FJi_Grouped3
import FJi_Grouped4
import FJi_Grouped5
import FJi_Grouped6
import FJi_Grouped7
import FJi_Reduction0
import FJi_Reduction1
import FJi_Reduction2
import FJi_Reduction3
import FJi_Reduction4
import FJi_Reduction5
import FJi_Reduction6
import FJi_Reduction7
import FJl_ActualObservations
import FJl_BaseLiteral
import FJl_ByteArray
import FJl_C1Coordinates
import FJl_C2Coordinates
import FJl_CMParser
import FJl_CallIndex
import FJl_CircleGeometry
import FJl_FixedIndex
import FJl_InnerReads
import FJl_LiteralW
import FJl_LoopExtraction
import FJl_M31ArrayValue
import FJl_M31Refine
import FJl_NativeCircle
import FJl_Nonvacuity
import FJl_Observation
import FJl_OpenedMeaning
import FJl_OpeningBytes
import FJl_OuterReads
import FJl_PackedInitial
import FJl_PackedInjective
import FJl_PackedSelected
import FJl_PairExtraction
import FJl_PowersCanonical
import FJl_PowersLiteral
import FJl_PreparedAlpha
import FJl_PreparedAtValues
import FJl_PreparedGamma
import FJl_QMArrayValue
import FJl_QMCodec
import FJl_QMParser
import FJl_QMSliceValue
import FJl_QMWindow
import FJl_QueryExtraction
import FJl_ReaderCanonical
import FJl_ReaderFields
import FJl_ReaderInspect
import FJl_ReaderPowers
import FJl_ScalarLiteral
import FJl_ScalarValues
import FJl_ScalarWindow
import FJl_SliceCopy
import FJl_SlotLiteral
import FJl_SlotReads
import FJl_SourceSlots
import FJl_Statements
import FJl_TailLiteral
import FJl_TailReads
import FJl_TailWindow0
import FJl_TailWindow1
import FJl_TailWindow2
import FJl_TermRead
import FJl_Tx1Extraction
import FJl_Tx2Extraction
import FJl_Tx2Values
import FJl_WindowArithmetic
import FJl_WordLane
import FJl_WordRead
import FJl_WordTails
import FJi_AllQueries
import ARX_Root

#print axioms AspisR1.FJl_ActualObservations.accepted
#print axioms AspisR1.FJl_BaseLiteral.value
#print axioms AspisR1.FJl_ByteArray.source
#print axioms AspisR1.FJl_ByteArray.list
#print axioms AspisR1.FJl_C1Coordinates.slot
#print axioms AspisR1.FJl_C1Coordinates.scalar
#print axioms AspisR1.FJl_C1Coordinates.tail
#print axioms AspisR1.FJl_C2Coordinates.slot
#print axioms AspisR1.FJl_C2Coordinates.coordinate
#print axioms AspisR1.FJl_CMParser.m31
#print axioms AspisR1.FJl_CMParser.source
#print axioms AspisR1.FJl_CallIndex.reached
#print axioms AspisR1.FJl_CircleGeometry.value
#print axioms AspisR1.FJl_FixedIndex.read
#print axioms AspisR1.FJl_InnerReads.value
#print axioms AspisR1.FJl_LiteralW.value
#print axioms AspisR1.FJl_LoopExtraction.native
#print axioms AspisR1.FJl_LoopExtraction.installed
#print axioms AspisR1.FJl_M31ArrayValue.value
#print axioms AspisR1.FJl_M31Refine.source
#print axioms AspisR1.FJl_M31Refine.value
#print axioms AspisR1.FJl_NativeCircle.value
#print axioms AspisR1.FJl_Nonvacuity.scalar
#print axioms AspisR1.FJl_Observation.reached
#print axioms AspisR1.FJl_OpenedMeaning.value
#print axioms AspisR1.FJl_OpeningBytes.value
#print axioms AspisR1.FJl_OuterReads.value
#print axioms AspisR1.FJl_PackedInitial.c1
#print axioms AspisR1.FJl_PackedInitial.c2
#print axioms AspisR1.FJl_PackedInjective.value
#print axioms AspisR1.FJl_PackedSelected.value
#print axioms AspisR1.FJl_PairExtraction.accepted
#print axioms AspisR1.FJl_PowersCanonical.value
#print axioms AspisR1.FJl_PowersCanonical.selected
#print axioms AspisR1.FJl_PowersLiteral.value
#print axioms AspisR1.FJl_PreparedAlpha.value
#print axioms AspisR1.FJl_PreparedAtValues.value
#print axioms AspisR1.FJl_PreparedGamma.value
#print axioms AspisR1.FJl_QMArrayValue.decoded
#print axioms AspisR1.FJl_QMArrayValue.bytes
#print axioms AspisR1.FJl_QMArrayValue.value
#print axioms AspisR1.FJl_QMCodec.decoded
#print axioms AspisR1.FJl_QMCodec.residue
#print axioms AspisR1.FJl_QMCodec.limbs
#print axioms AspisR1.FJl_QMParser.source
#print axioms AspisR1.FJl_QMSliceValue.value
#print axioms AspisR1.FJl_QMWindow.value
#print axioms AspisR1.FJl_QueryExtraction.accepted
#print axioms AspisR1.FJl_ReaderCanonical.read
#print axioms AspisR1.FJl_ReaderFields.value
#print axioms AspisR1.FJl_ReaderPowers.value
#print axioms AspisR1.FJl_ScalarLiteral.value
#print axioms AspisR1.FJl_ScalarValues.value
#print axioms AspisR1.FJl_ScalarWindow.reached
#print axioms AspisR1.FJl_SliceCopy.bytes
#print axioms AspisR1.FJl_SliceCopy.scalar
#print axioms AspisR1.FJl_SlotLiteral.value
#print axioms AspisR1.FJl_SlotReads.reached
#print axioms AspisR1.FJl_SourceSlots.installed
#print axioms AspisR1.FJl_TailLiteral.c1
#print axioms AspisR1.FJl_TailLiteral.c2first
#print axioms AspisR1.FJl_TailLiteral.c2second
#print axioms AspisR1.FJl_TailReads.reached
#print axioms AspisR1.FJl_TailWindow0.value
#print axioms AspisR1.FJl_TailWindow1.value
#print axioms AspisR1.FJl_TailWindow2.value
#print axioms AspisR1.FJl_TermRead.value
#print axioms AspisR1.FJl_Tx1Extraction.reached
#print axioms AspisR1.FJl_Tx2Extraction.reached
#print axioms AspisR1.FJl_Tx2Values.accepted
#print axioms AspisR1.FJl_WindowArithmetic.scalar
#print axioms AspisR1.FJl_WindowArithmetic.c1tail
#print axioms AspisR1.FJl_WindowArithmetic.c2
#print axioms AspisR1.FJl_WordLane.leaf
#print axioms AspisR1.FJl_WordLane.slot
#print axioms AspisR1.FJl_WordLane.scalar
#print axioms AspisR1.FJl_WordRead.value
#print axioms AspisR1.FJl_WordTails.c1
#print axioms AspisR1.FJl_WordTails.c2first
#print axioms AspisR1.FJl_WordTails.c2second
#print axioms AspisR1.FJi_AllQueries.value
#print axioms AspisR1.ARX_Root.deployed
#print axioms AspisR1.FJi_Grouped0.value
#print axioms AspisR1.FJi_Reduction0.value
#print axioms AspisR1.FJi_Grouped1.value
#print axioms AspisR1.FJi_Reduction1.value
#print axioms AspisR1.FJi_Grouped2.value
#print axioms AspisR1.FJi_Reduction2.value
#print axioms AspisR1.FJi_Grouped3.value
#print axioms AspisR1.FJi_Reduction3.value
#print axioms AspisR1.FJi_Grouped4.value
#print axioms AspisR1.FJi_Reduction4.value
#print axioms AspisR1.FJi_Grouped5.value
#print axioms AspisR1.FJi_Reduction5.value
#print axioms AspisR1.FJi_Grouped6.value
#print axioms AspisR1.FJi_Reduction6.value
#print axioms AspisR1.FJi_Grouped7.value
#print axioms AspisR1.FJi_Reduction7.value
#print axioms AspisR1.FJi_Query00.value
#print axioms AspisR1.FJi_Query01.value
#print axioms AspisR1.FJi_Query02.value
#print axioms AspisR1.FJi_Query03.value
#print axioms AspisR1.FJi_Query04.value
#print axioms AspisR1.FJi_Query05.value
#print axioms AspisR1.FJi_Query06.value
#print axioms AspisR1.FJi_Query07.value
#print axioms AspisR1.FJi_Query08.value
#print axioms AspisR1.FJi_Query09.value
#print axioms AspisR1.FJi_Query10.value
#print axioms AspisR1.FJi_Query11.value
#print axioms AspisR1.FJi_Query12.value
#print axioms AspisR1.FJi_Query13.value
#print axioms AspisR1.FJi_Query14.value
#print axioms AspisR1.FJi_Query15.value
#print axioms AspisR1.FJi_Query16.value
#print axioms AspisR1.FJi_Query17.value
#print axioms AspisR1.FJi_Query18.value
#print axioms AspisR1.FJi_Query19.value
#print axioms AspisR1.FJi_Query20.value
#print axioms AspisR1.FJi_Query21.value
