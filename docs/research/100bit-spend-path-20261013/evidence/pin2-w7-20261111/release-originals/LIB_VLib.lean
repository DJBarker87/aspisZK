import LIB_VField
import LIB_VRecordsAll
import LIB_VParse
import LIB_VSemantic
import LIBC_VPrepare
import LIB_VTx1A
import LIBC_VTx1B
import LIBC_CheckValuesDomain
set_option autoImplicit false
noncomputable section
namespace LIB_VLib
open RSL
/-- The canonical TX1 library, assembled only from the merged concrete fields. -/
def library : VLib where
 Public := LIB_VCarriers.Public
 Prefix := LIB_VCarriers.Prefix
 Transcript := LIB_VCarriers.Transcript
 Challenges := LIB_VCarriers.Challenges
 OrigChallenges := LIB_VCarriers.OrigChallenges
 QM31 := LIB_VCarriers.QM31
 Alpha := LIB_VCarriers.Alpha
 Claims := LIB_VCarriers.Claims
 K29 := LIB_VCarriers.K29
 Point := LIB_VCarriers.Point
 Record := LIB_VCarriers.Record
 WErr := LIB_VCarriers.WErr
 VErr := LIB_VCarriers.VErr
 CodecErr := LIB_VCarriers.CodecErr
 View := LIB_VCarriers.View
 Prepared := LIB_VCarriers.Prepared
 E29 := LIB_VCarriers.E29
 Acc := LIB_VCarriers.Acc
 Geo := LIB_VCarriers.Geo
 Weights := LIB_VCarriers.Weights
 qDec := LIB_VCarriers.qDec
 pDec := LIB_VCarriers.pDec
 wTerminal := LIB_VCarriers.wTerminal
 wEqualCirclePoints := LIB_VCarriers.wEqualCirclePoints
 wPublic := LIB_VCarriers.wPublic
 vParse := LIB_VCarriers.vParse
 vSemantic := LIB_VCarriers.vSemantic
 vAllocation := LIB_VCarriers.vAllocation
 codecToV := LIB_VCarriers.codecToV
 debugV := LIB_VCarriers.debugV
 finishInputDom := LIB_VSemantic.finishInputDom
 publicDom := LIB_VSemantic.publicDom
 semanticBytesDom := LIB_VParse.semanticBytesDom
 checkValuesDom := LIBC_CheckValuesDomain.checkValuesDom
 semanticRounds := LIB_VSemantic.semanticRounds
 claims := LIB_VSemantic.claims
 origChallenges := LIB_VCarriers.origChallenges
 terminalQm31 := LIB_VSemantic.terminalQm31
 maskValue := LIB_VField.maskValue
 validatedRecord := LIB_VRecordsAll.validatedRecord
 decodeK29 := LIB_VRecordsAll.decodeK29
 eta := LIB_VCarriers.eta
 qadd := LIB_VField.qadd
 qmul := LIB_VField.qmul
 at28 := LIB_VCarriers.at28
 state := LIB_VRecordsAll.state
 circle := LIB_VSemantic.circle
 payload := LIB_VRecordsAll.payload
 c1Root := LIB_VCarriers.c1Root
 parsePrefix := LIB_VParse.parsePrefix
 publicTranscript := LIB_VParse.publicTranscript
 begin := LIB_VParse.begin_
 filled := LIBC_VPrepare.filled
 expandSemantic := LIBC_VPrepare.expandSemantic
 expandValues := LIBC_VPrepare.expandValues
 wideView := LIBC_VPrepare.wideView
 viewSemantic := LIB_VCarriers.viewSemantic
 parseShape := LIB_VTx1A.parseShape
 canonicalScan := LIBC_VTx1A.canonicalScan
 zeroE29 := LIB_VCarriers.zeroE29
 accNew := LIBC_VTx1A.accNew
 batchMerkle := LIBC_VTx1B.batchMerkle
 geometry := LIBC_VTx1B.geometry
 weightsNew := LIBC_VTx1A.weightsNew
 queryLoop := LIBC_VTx1B.queryLoop
 finish := LIBC_VTx1A.finish
 checkpoint := LIBC_VTx1B.checkpoint
theorem Public_exact : library.Public = LIB_VCarriers.Public := rfl
#print axioms Public_exact
theorem Prefix_exact : library.Prefix = LIB_VCarriers.Prefix := rfl
#print axioms Prefix_exact
theorem Transcript_exact : library.Transcript = LIB_VCarriers.Transcript := rfl
#print axioms Transcript_exact
theorem Challenges_exact : library.Challenges = LIB_VCarriers.Challenges := rfl
#print axioms Challenges_exact
theorem OrigChallenges_exact : library.OrigChallenges = LIB_VCarriers.OrigChallenges := rfl
#print axioms OrigChallenges_exact
theorem QM31_exact : library.QM31 = LIB_VCarriers.QM31 := rfl
#print axioms QM31_exact
theorem Alpha_exact : library.Alpha = LIB_VCarriers.Alpha := rfl
#print axioms Alpha_exact
theorem Claims_exact : library.Claims = LIB_VCarriers.Claims := rfl
#print axioms Claims_exact
theorem K29_exact : library.K29 = LIB_VCarriers.K29 := rfl
#print axioms K29_exact
theorem Point_exact : library.Point = LIB_VCarriers.Point := rfl
#print axioms Point_exact
theorem Record_exact : library.Record = LIB_VCarriers.Record := rfl
#print axioms Record_exact
theorem WErr_exact : library.WErr = LIB_VCarriers.WErr := rfl
#print axioms WErr_exact
theorem VErr_exact : library.VErr = LIB_VCarriers.VErr := rfl
#print axioms VErr_exact
theorem CodecErr_exact : library.CodecErr = LIB_VCarriers.CodecErr := rfl
#print axioms CodecErr_exact
theorem View_exact : library.View = LIB_VCarriers.View := rfl
#print axioms View_exact
theorem Prepared_exact : library.Prepared = LIB_VCarriers.Prepared := rfl
#print axioms Prepared_exact
theorem E29_exact : library.E29 = LIB_VCarriers.E29 := rfl
#print axioms E29_exact
theorem Acc_exact : library.Acc = LIB_VCarriers.Acc := rfl
#print axioms Acc_exact
theorem Geo_exact : library.Geo = LIB_VCarriers.Geo := rfl
#print axioms Geo_exact
theorem Weights_exact : library.Weights = LIB_VCarriers.Weights := rfl
#print axioms Weights_exact
theorem wTerminal_exact : library.wTerminal = LIB_VCarriers.wTerminal := rfl
#print axioms wTerminal_exact
theorem wEqualCirclePoints_exact : library.wEqualCirclePoints = LIB_VCarriers.wEqualCirclePoints := rfl
#print axioms wEqualCirclePoints_exact
theorem wPublic_exact : library.wPublic = LIB_VCarriers.wPublic := rfl
#print axioms wPublic_exact
theorem vParse_exact : library.vParse = LIB_VCarriers.vParse := rfl
#print axioms vParse_exact
theorem vSemantic_exact : library.vSemantic = LIB_VCarriers.vSemantic := rfl
#print axioms vSemantic_exact
theorem vAllocation_exact : library.vAllocation = LIB_VCarriers.vAllocation := rfl
#print axioms vAllocation_exact
theorem codecToV_exact : library.codecToV = LIB_VCarriers.codecToV := rfl
#print axioms codecToV_exact
theorem debugV_exact : library.debugV = LIB_VCarriers.debugV := rfl
#print axioms debugV_exact
theorem finishInputDom_exact : library.finishInputDom = LIB_VSemantic.finishInputDom := rfl
#print axioms finishInputDom_exact
theorem publicDom_exact : library.publicDom = LIB_VSemantic.publicDom := rfl
#print axioms publicDom_exact
theorem semanticBytesDom_exact : library.semanticBytesDom = LIB_VParse.semanticBytesDom := rfl
#print axioms semanticBytesDom_exact
theorem checkValuesDom_exact : library.checkValuesDom = LIBC_CheckValuesDomain.checkValuesDom := rfl
#print axioms checkValuesDom_exact
theorem semanticRounds_exact : library.semanticRounds = LIB_VSemantic.semanticRounds := rfl
#print axioms semanticRounds_exact
theorem claims_exact : library.claims = LIB_VSemantic.claims := rfl
#print axioms claims_exact
theorem origChallenges_exact : library.origChallenges = LIB_VCarriers.origChallenges := rfl
#print axioms origChallenges_exact
theorem terminalQm31_exact : library.terminalQm31 = LIB_VSemantic.terminalQm31 := rfl
#print axioms terminalQm31_exact
theorem maskValue_exact : library.maskValue = LIB_VField.maskValue := rfl
#print axioms maskValue_exact
theorem validatedRecord_exact : library.validatedRecord = LIB_VRecordsAll.validatedRecord := rfl
#print axioms validatedRecord_exact
theorem decodeK29_exact : library.decodeK29 = LIB_VRecordsAll.decodeK29 := rfl
#print axioms decodeK29_exact
theorem eta_exact : library.eta = LIB_VCarriers.eta := rfl
#print axioms eta_exact
theorem qadd_exact : library.qadd = LIB_VField.qadd := rfl
#print axioms qadd_exact
theorem qmul_exact : library.qmul = LIB_VField.qmul := rfl
#print axioms qmul_exact
theorem at28_exact : library.at28 = LIB_VCarriers.at28 := rfl
#print axioms at28_exact
theorem state_exact : library.state = LIB_VRecordsAll.state := rfl
#print axioms state_exact
theorem circle_exact : library.circle = LIB_VSemantic.circle := rfl
#print axioms circle_exact
theorem payload_exact : library.payload = LIB_VRecordsAll.payload := rfl
#print axioms payload_exact
theorem c1Root_exact : library.c1Root = LIB_VCarriers.c1Root := rfl
#print axioms c1Root_exact
theorem parsePrefix_exact : library.parsePrefix = LIB_VParse.parsePrefix := rfl
#print axioms parsePrefix_exact
theorem publicTranscript_exact : library.publicTranscript = LIB_VParse.publicTranscript := rfl
#print axioms publicTranscript_exact
theorem begin_exact : library.begin = LIB_VParse.begin_ := rfl
#print axioms begin_exact
theorem filled_exact : library.filled = LIBC_VPrepare.filled := rfl
#print axioms filled_exact
theorem expandSemantic_exact : library.expandSemantic = LIBC_VPrepare.expandSemantic := rfl
#print axioms expandSemantic_exact
theorem expandValues_exact : library.expandValues = LIBC_VPrepare.expandValues := rfl
#print axioms expandValues_exact
theorem wideView_exact : library.wideView = LIBC_VPrepare.wideView := rfl
#print axioms wideView_exact
theorem viewSemantic_exact : library.viewSemantic = LIB_VCarriers.viewSemantic := rfl
#print axioms viewSemantic_exact
theorem parseShape_exact : library.parseShape = LIB_VTx1A.parseShape := rfl
#print axioms parseShape_exact
theorem canonicalScan_exact : library.canonicalScan = LIBC_VTx1A.canonicalScan := rfl
#print axioms canonicalScan_exact
theorem zeroE29_exact : library.zeroE29 = LIB_VCarriers.zeroE29 := rfl
#print axioms zeroE29_exact
theorem accNew_exact : library.accNew = LIBC_VTx1A.accNew := rfl
#print axioms accNew_exact
theorem batchMerkle_exact : library.batchMerkle = LIBC_VTx1B.batchMerkle := rfl
#print axioms batchMerkle_exact
theorem geometry_exact : library.geometry = LIBC_VTx1B.geometry := rfl
#print axioms geometry_exact
theorem weightsNew_exact : library.weightsNew = LIBC_VTx1A.weightsNew := rfl
#print axioms weightsNew_exact
theorem queryLoop_exact : library.queryLoop = LIBC_VTx1B.queryLoop := rfl
#print axioms queryLoop_exact
theorem finish_exact : library.finish = LIBC_VTx1A.finish := rfl
#print axioms finish_exact
theorem checkpoint_exact : library.checkpoint = LIBC_VTx1B.checkpoint := rfl
#print axioms checkpoint_exact
theorem qDec_exact : library.qDec = LIB_VCarriers.qDec := rfl
#print axioms qDec_exact
theorem pDec_exact : library.pDec = LIB_VCarriers.pDec := rfl
#print axioms pDec_exact
def semanticRoundsValue (a : LIB_VCarriers.Prefix × LIB_VCarriers.Transcript) (env : Env) := LIB_VRounds.eval a env
theorem semanticRounds_returns (a : LIB_VCarriers.Prefix × LIB_VCarriers.Transcript) (env : Env) : NND_Returned.Returns (library.semanticRounds.law a) env (semanticRoundsValue a env) := LIB_VRounds.returns a env
#print axioms semanticRounds_returns
def claimsValue (a : LIB_VCarriers.Prefix) (env : Env) := LIB_VClaims.eval a env
theorem claims_returns (a : LIB_VCarriers.Prefix) (env : Env) : NND_Returned.Returns (library.claims.law a) env (claimsValue a env) := LIB_VClaims.returns a env
#print axioms claims_returns
def terminalQm31Value (a : LIB_VCarriers.Public × LIB_VCarriers.Claims × LIB_VCarriers.Alpha × LIB_VCarriers.OrigChallenges) (env : Env) := LIB_VTerminal.eval a
theorem terminalQm31_returns (a : LIB_VCarriers.Public × LIB_VCarriers.Claims × LIB_VCarriers.Alpha × LIB_VCarriers.OrigChallenges) (env : Env) : NND_Returned.Returns (library.terminalQm31.law a) env (terminalQm31Value a env) := LIB_VTerminal.returns a env
#print axioms terminalQm31_returns
def circleValue (a : LIB_VCarriers.Transcript × LIB_VCarriers.Record) (env : Env) := LIB_VCircle.eval a env
theorem circle_returns (a : LIB_VCarriers.Transcript × LIB_VCarriers.Record) (env : Env) : NND_Returned.Returns (library.circle.law a) env (circleValue a env) := LIB_VCircle.returns a env
#print axioms circle_returns
def parsePrefixValue (a : Bytes) (env : Env) := LIB_VParsePrefix.eval a
theorem parsePrefix_returns (a : Bytes) (env : Env) : NND_Returned.Returns (library.parsePrefix.law a) env (parsePrefixValue a env) := LIB_VParsePrefix.returns a env
#print axioms parsePrefix_returns
def publicTranscriptValue (a : LIB_VCarriers.Public × B32) (env : Env) := LIB_VPublicTranscript.eval a env
theorem publicTranscript_returns (a : LIB_VCarriers.Public × B32) (env : Env) : NND_Returned.Returns (library.publicTranscript.law a) env (publicTranscriptValue a env) := LIB_VPublicTranscript.returns a env
#print axioms publicTranscript_returns
def beginValue (a : LIB_VCarriers.Prefix × LIB_VCarriers.Transcript) (env : Env) := LIB_VBegin.eval a env
theorem begin_returns (a : LIB_VCarriers.Prefix × LIB_VCarriers.Transcript) (env : Env) : NND_Returned.Returns (library.begin.law a) env (beginValue a env) := LIB_VBegin.returns a env
#print axioms begin_returns
def filledValue (a : Nat) (env : Env) := LIBC_Filled.value a env
theorem filled_returns (a : Nat) (env : Env) : NND_Returned.Returns (library.filled.law a) env (filledValue a env) := LIBC_Filled.returns a env
#print axioms filled_returns
def expandSemanticValue (a : Bytes × Bytes) (env : Env) := LIBC_ExpandSemantic.value a env
theorem expandSemantic_returns (a : Bytes × Bytes) (env : Env) : NND_Returned.Returns (library.expandSemantic.law a) env (expandSemanticValue a env) := LIBC_ExpandSemantic.returns a env
#print axioms expandSemantic_returns
def expandValuesValue (a : Bytes × Bytes) (env : Env) := LIBC_ExpandValues.value a env
theorem expandValues_returns (a : Bytes × Bytes) (env : Env) : NND_Returned.Returns (library.expandValues.law a) env (expandValuesValue a env) := LIBC_ExpandValues.returns a env
#print axioms expandValues_returns
def wideViewValue (a : Bytes × Bytes × Bytes) (env : Env) := LIBC_WideView.value a env
theorem wideView_returns (a : Bytes × Bytes × Bytes) (env : Env) : NND_Returned.Returns (library.wideView.law a) env (wideViewValue a env) := LIBC_WideView.returns a env
#print axioms wideView_returns
def parseShapeValue (a : Bytes) (env : Env) := LIBC_ParseShape.value a env
theorem parseShape_returns (a : Bytes) (env : Env) : NND_Returned.Returns (library.parseShape.law a) env (parseShapeValue a env) := LIB_ParseShapeTotal.returns a env
#print axioms parseShape_returns
def canonicalScanValue (a : Bytes) (env : Env) := LIBC_CanonicalScan.value a env
theorem canonicalScan_returns (a : Bytes) (env : Env) : NND_Returned.Returns (library.canonicalScan.law a) env (canonicalScanValue a env) := LIBC_CanonicalScan.returns a env
#print axioms canonicalScan_returns
def accNewValue (a : Unit) (env : Env) := LIBC_AccNew.value env
theorem accNew_returns (a : Unit) (env : Env) : NND_Returned.Returns (library.accNew.law a) env (accNewValue a env) := by cases a; exact LIBC_AccNew.returns env
#print axioms accNew_returns
def weightsNewValue (a : LIB_VCarriers.Acc) (env : Env) := LIBC_WeightsNew.value a env
theorem weightsNew_returns (a : LIB_VCarriers.Acc) (env : Env) : NND_Returned.Returns (library.weightsNew.law a) env (weightsNewValue a env) := LIBC_WeightsNew.returns a env
#print axioms weightsNew_returns
def finishValue (a : LIBC_Finish.Args) (env : Env) := LIBC_Finish.value a env
theorem finish_returns (a : LIBC_Finish.Args) (env : Env) : NND_Returned.Returns (library.finish.law a) env (finishValue a env) := LIBC_Finish.returns a env
#print axioms finish_returns
def batchMerkleValue (a : LIBC_BatchMerkle.Args) (env : Env) := LIBC_BatchMerkle.value a env
theorem batchMerkle_returns (a : LIBC_BatchMerkle.Args) (env : Env) : NND_Returned.Returns (library.batchMerkle.law a) env (batchMerkleValue a env) := LIBC_BatchMerkle.returns a env
#print axioms batchMerkle_returns
def geometryValue (a : LIBC_Geometry.Args) (env : Env) := LIBC_Geometry.value a env
theorem geometry_returns (a : LIBC_Geometry.Args) (env : Env) : NND_Returned.Returns (library.geometry.law a) env (geometryValue a env) := LIBC_Geometry.returns a env
#print axioms geometry_returns
def queryLoopValue (a : LIBC_QueryLoop.Args) (env : Env) := LIBC_QueryLoop.value a env
theorem queryLoop_returns (a : LIBC_QueryLoop.Args) (env : Env) : NND_Returned.Returns (library.queryLoop.law a) env (queryLoopValue a env) := LIBC_QueryLoop.returns a env
#print axioms queryLoop_returns
def checkpointValue (a : LIBC_Checkpoint.Args) (env : Env) := LIBC_Checkpoint.value a env
theorem checkpoint_returns (a : LIBC_Checkpoint.Args) (env : Env) : NND_Returned.Returns (library.checkpoint.law a) env (checkpointValue a env) := LIBC_Checkpoint.returns a env
#print axioms checkpoint_returns
theorem reservation_functional : Child.Functional library.claims ∧ Child.Functional library.filled ∧ Child.Functional library.accNew ∧ Child.Functional library.weightsNew :=
 ⟨LIB_VClaims.functional,LIBC_Filled.functional,LIBC_AccNew.functional,LIBC_WeightsNew.functional⟩
#print axioms reservation_functional
end LIB_VLib
