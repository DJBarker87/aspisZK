import ARX_Root
import JGl_FinalAudit
import JGi_TX1Ready
import JGn_ActiveData
import JGn_ActiveMath
import JGn_ActiveNumeric
import JGn_CompositionValue
import JGn_CopyCanonical
import JGn_CopyChunk00
import JGn_CopyChunk01
import JGn_CopyChunk02
import JGn_CopyChunk03
import JGn_CopyChunk04
import JGn_CopyChunk05
import JGn_CopyChunk06
import JGn_CopyChunk07
import JGn_CopyChunk08
import JGn_CopyChunk09
import JGn_CopyChunk10
import JGn_CopyChunk11
import JGn_CopyChunk12
import JGn_CopyChunk13
import JGn_CopyChunk14
import JGn_CopyChunk15
import JGn_CopyChunk16
import JGn_CopyData
import JGn_CopyFold
import JGn_CopyNumeric
import JGn_CopyPatterns
import JGn_CopyPower04
import JGn_CopyPower08
import JGn_CopyPower12
import JGn_CopyPower16
import JGn_CopyPowers
import JGn_CopyRows
import JGn_CurrentPreparation
import JGn_ExactEval
import JGn_ExactPreflight
import JGn_FieldExact
import JGn_FullEven
import JGn_FullFinal
import JGn_FullMath
import JGn_FullMid
import JGn_FullNumeric
import JGn_FullOdd
import JGn_FullPhaseData
import JGn_FullPow0
import JGn_FullPow1
import JGn_LeadingNumeric
import JGn_MaskedAcceptance
import JGn_PatternMath
import JGn_PoseidonNumeric
import JGn_PrefixEval
import JGn_PrefixPreflight
import JGn_PrepareBuffer
import JGn_PrepareInspect
import JGn_PrepareLayoutInspect
import JGn_SelectedHelper
import JGn_SplitSource
import JGn_TerminalArithmetic
import JGn_TerminalData
import JGn_TerminalEquality
import JGn_TerminalIdentified
import JGn_TerminalLow
import JGn_TerminalPowers
set_option autoImplicit false
namespace AspisR1.JGn_TX1Prefix
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation FirstComposition
open AspisR1ClaimPreparedBridge
/-- The exact existing SAME-byte readiness theorem with its terminal guard
proved. This is not enclosing candidate.prepare, accepted1 or writer identity. -/
theorem inhabited {C H : Type} (ops : Ops) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    let D0 := F3V_OracleDictionary.current JFp_SHADigest.digest D
    let installed := WAdm_Execution.actual ops true query geo JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix) (view : verifier.View)
      (sem : r1_semantic.Verified H) (out : verifier.Prepared)
      (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
      AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
        JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
        D0 (toCurrentPublic JFs_PublicSerialization.value) expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D0 sem view hash input=ok (.Ok out,scratch) ∧
      verifier.candidate.tx1 installed D0 (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize hash none=
        JGi_TX1Control.afterScan installed D0 (toCurrentPublic JFs_PublicSerialization.value)
          JFx_NativeBytes.publicInput JFx_NativeBytes.proof hash := by
  exact JGi_TX1Ready.inhabited ops query geo D hash input JGn_TerminalIdentified.identified
#print axioms inhabited
end AspisR1.JGn_TX1Prefix
#print axioms AspisR1.JGn_ActiveMath.chunk0
#print axioms AspisR1.JGn_ActiveMath.chunk1
#print axioms AspisR1.JGn_ActiveMath.chunk2
#print axioms AspisR1.JGn_ActiveMath.chunk3
#print axioms AspisR1.JGn_ActiveMath.chunk4
#print axioms AspisR1.JGn_ActiveMath.chunk5
#print axioms AspisR1.JGn_ActiveMath.chunk6
#print axioms AspisR1.JGn_ActiveMath.chunk7
#print axioms AspisR1.JGn_ActiveMath.value
#print axioms AspisR1.JGn_ActiveNumeric.canonical
#print axioms AspisR1.JGn_ActiveNumeric.source
#print axioms AspisR1.JGn_CompositionValue.value
#print axioms AspisR1.JGn_CopyCanonical.patterns
#print axioms AspisR1.JGn_CopyChunk00.pv0
#print axioms AspisR1.JGn_CopyChunk00.pv1
#print axioms AspisR1.JGn_CopyChunk00.pw0
#print axioms AspisR1.JGn_CopyChunk00.pw1
#print axioms AspisR1.JGn_CopyChunk00.cv0
#print axioms AspisR1.JGn_CopyChunk00.cv1
#print axioms AspisR1.JGn_CopyChunk00.cw0
#print axioms AspisR1.JGn_CopyChunk00.cw1
#print axioms AspisR1.JGn_CopyChunk00.value
#print axioms AspisR1.JGn_CopyChunk01.pv0
#print axioms AspisR1.JGn_CopyChunk01.pv1
#print axioms AspisR1.JGn_CopyChunk01.pw0
#print axioms AspisR1.JGn_CopyChunk01.pw1
#print axioms AspisR1.JGn_CopyChunk01.cv0
#print axioms AspisR1.JGn_CopyChunk01.cv1
#print axioms AspisR1.JGn_CopyChunk01.cw0
#print axioms AspisR1.JGn_CopyChunk01.cw1
#print axioms AspisR1.JGn_CopyChunk01.value
#print axioms AspisR1.JGn_CopyChunk02.pv0
#print axioms AspisR1.JGn_CopyChunk02.pv1
#print axioms AspisR1.JGn_CopyChunk02.pw0
#print axioms AspisR1.JGn_CopyChunk02.pw1
#print axioms AspisR1.JGn_CopyChunk02.cv0
#print axioms AspisR1.JGn_CopyChunk02.cv1
#print axioms AspisR1.JGn_CopyChunk02.cw0
#print axioms AspisR1.JGn_CopyChunk02.cw1
#print axioms AspisR1.JGn_CopyChunk02.value
#print axioms AspisR1.JGn_CopyChunk03.pv0
#print axioms AspisR1.JGn_CopyChunk03.pv1
#print axioms AspisR1.JGn_CopyChunk03.pw0
#print axioms AspisR1.JGn_CopyChunk03.pw1
#print axioms AspisR1.JGn_CopyChunk03.cv0
#print axioms AspisR1.JGn_CopyChunk03.cv1
#print axioms AspisR1.JGn_CopyChunk03.cw0
#print axioms AspisR1.JGn_CopyChunk03.cw1
#print axioms AspisR1.JGn_CopyChunk03.value
#print axioms AspisR1.JGn_CopyChunk04.pv0
#print axioms AspisR1.JGn_CopyChunk04.pv1
#print axioms AspisR1.JGn_CopyChunk04.pw0
#print axioms AspisR1.JGn_CopyChunk04.pw1
#print axioms AspisR1.JGn_CopyChunk04.cv0
#print axioms AspisR1.JGn_CopyChunk04.cv1
#print axioms AspisR1.JGn_CopyChunk04.cw0
#print axioms AspisR1.JGn_CopyChunk04.cw1
#print axioms AspisR1.JGn_CopyChunk04.value
#print axioms AspisR1.JGn_CopyChunk05.pv0
#print axioms AspisR1.JGn_CopyChunk05.pv1
#print axioms AspisR1.JGn_CopyChunk05.pw0
#print axioms AspisR1.JGn_CopyChunk05.pw1
#print axioms AspisR1.JGn_CopyChunk05.cv0
#print axioms AspisR1.JGn_CopyChunk05.cv1
#print axioms AspisR1.JGn_CopyChunk05.cw0
#print axioms AspisR1.JGn_CopyChunk05.cw1
#print axioms AspisR1.JGn_CopyChunk05.value
#print axioms AspisR1.JGn_CopyChunk06.pv0
#print axioms AspisR1.JGn_CopyChunk06.pv1
#print axioms AspisR1.JGn_CopyChunk06.pw0
#print axioms AspisR1.JGn_CopyChunk06.pw1
#print axioms AspisR1.JGn_CopyChunk06.cv0
#print axioms AspisR1.JGn_CopyChunk06.cv1
#print axioms AspisR1.JGn_CopyChunk06.cw0
#print axioms AspisR1.JGn_CopyChunk06.cw1
#print axioms AspisR1.JGn_CopyChunk06.value
#print axioms AspisR1.JGn_CopyChunk07.pv0
#print axioms AspisR1.JGn_CopyChunk07.pv1
#print axioms AspisR1.JGn_CopyChunk07.pw0
#print axioms AspisR1.JGn_CopyChunk07.pw1
#print axioms AspisR1.JGn_CopyChunk07.cv0
#print axioms AspisR1.JGn_CopyChunk07.cv1
#print axioms AspisR1.JGn_CopyChunk07.cw0
#print axioms AspisR1.JGn_CopyChunk07.cw1
#print axioms AspisR1.JGn_CopyChunk07.value
#print axioms AspisR1.JGn_CopyChunk08.pv0
#print axioms AspisR1.JGn_CopyChunk08.pv1
#print axioms AspisR1.JGn_CopyChunk08.pw0
#print axioms AspisR1.JGn_CopyChunk08.pw1
#print axioms AspisR1.JGn_CopyChunk08.cv0
#print axioms AspisR1.JGn_CopyChunk08.cv1
#print axioms AspisR1.JGn_CopyChunk08.cw0
#print axioms AspisR1.JGn_CopyChunk08.cw1
#print axioms AspisR1.JGn_CopyChunk08.value
#print axioms AspisR1.JGn_CopyChunk09.pv0
#print axioms AspisR1.JGn_CopyChunk09.pv1
#print axioms AspisR1.JGn_CopyChunk09.pw0
#print axioms AspisR1.JGn_CopyChunk09.pw1
#print axioms AspisR1.JGn_CopyChunk09.cv0
#print axioms AspisR1.JGn_CopyChunk09.cv1
#print axioms AspisR1.JGn_CopyChunk09.cw0
#print axioms AspisR1.JGn_CopyChunk09.cw1
#print axioms AspisR1.JGn_CopyChunk09.value
#print axioms AspisR1.JGn_CopyChunk10.pv0
#print axioms AspisR1.JGn_CopyChunk10.pv1
#print axioms AspisR1.JGn_CopyChunk10.pw0
#print axioms AspisR1.JGn_CopyChunk10.pw1
#print axioms AspisR1.JGn_CopyChunk10.cv0
#print axioms AspisR1.JGn_CopyChunk10.cv1
#print axioms AspisR1.JGn_CopyChunk10.cw0
#print axioms AspisR1.JGn_CopyChunk10.cw1
#print axioms AspisR1.JGn_CopyChunk10.value
#print axioms AspisR1.JGn_CopyChunk11.pv0
#print axioms AspisR1.JGn_CopyChunk11.pv1
#print axioms AspisR1.JGn_CopyChunk11.pw0
#print axioms AspisR1.JGn_CopyChunk11.pw1
#print axioms AspisR1.JGn_CopyChunk11.cv0
#print axioms AspisR1.JGn_CopyChunk11.cv1
#print axioms AspisR1.JGn_CopyChunk11.cw0
#print axioms AspisR1.JGn_CopyChunk11.cw1
#print axioms AspisR1.JGn_CopyChunk11.value
#print axioms AspisR1.JGn_CopyChunk12.pv0
#print axioms AspisR1.JGn_CopyChunk12.pv1
#print axioms AspisR1.JGn_CopyChunk12.pw0
#print axioms AspisR1.JGn_CopyChunk12.pw1
#print axioms AspisR1.JGn_CopyChunk12.cv0
#print axioms AspisR1.JGn_CopyChunk12.cv1
#print axioms AspisR1.JGn_CopyChunk12.cw0
#print axioms AspisR1.JGn_CopyChunk12.cw1
#print axioms AspisR1.JGn_CopyChunk12.value
#print axioms AspisR1.JGn_CopyChunk13.pv0
#print axioms AspisR1.JGn_CopyChunk13.pv1
#print axioms AspisR1.JGn_CopyChunk13.pw0
#print axioms AspisR1.JGn_CopyChunk13.pw1
#print axioms AspisR1.JGn_CopyChunk13.cv0
#print axioms AspisR1.JGn_CopyChunk13.cv1
#print axioms AspisR1.JGn_CopyChunk13.cw0
#print axioms AspisR1.JGn_CopyChunk13.cw1
#print axioms AspisR1.JGn_CopyChunk13.value
#print axioms AspisR1.JGn_CopyChunk14.pv0
#print axioms AspisR1.JGn_CopyChunk14.pv1
#print axioms AspisR1.JGn_CopyChunk14.pw0
#print axioms AspisR1.JGn_CopyChunk14.pw1
#print axioms AspisR1.JGn_CopyChunk14.cv0
#print axioms AspisR1.JGn_CopyChunk14.cv1
#print axioms AspisR1.JGn_CopyChunk14.cw0
#print axioms AspisR1.JGn_CopyChunk14.cw1
#print axioms AspisR1.JGn_CopyChunk14.value
#print axioms AspisR1.JGn_CopyChunk15.pv0
#print axioms AspisR1.JGn_CopyChunk15.pv1
#print axioms AspisR1.JGn_CopyChunk15.pw0
#print axioms AspisR1.JGn_CopyChunk15.pw1
#print axioms AspisR1.JGn_CopyChunk15.cv0
#print axioms AspisR1.JGn_CopyChunk15.cv1
#print axioms AspisR1.JGn_CopyChunk15.cw0
#print axioms AspisR1.JGn_CopyChunk15.cw1
#print axioms AspisR1.JGn_CopyChunk15.value
#print axioms AspisR1.JGn_CopyChunk16.pv0
#print axioms AspisR1.JGn_CopyChunk16.pv1
#print axioms AspisR1.JGn_CopyChunk16.pw0
#print axioms AspisR1.JGn_CopyChunk16.pw1
#print axioms AspisR1.JGn_CopyChunk16.cv0
#print axioms AspisR1.JGn_CopyChunk16.cv1
#print axioms AspisR1.JGn_CopyChunk16.cw0
#print axioms AspisR1.JGn_CopyChunk16.cw1
#print axioms AspisR1.JGn_CopyChunk16.value
#print axioms AspisR1.JGn_CopyFold.value
#print axioms AspisR1.JGn_CopyNumeric.helperCanonical
#print axioms AspisR1.JGn_CopyNumeric.residualCanonical
#print axioms AspisR1.JGn_CopyNumeric.model
#print axioms AspisR1.JGn_CopyNumeric.identified
#print axioms AspisR1.JGn_CopyPatterns.powersCanonical
#print axioms AspisR1.JGn_CopyPatterns.identified
#print axioms AspisR1.JGn_CopyPatterns.source
#print axioms AspisR1.JGn_CopyPower04.source
#print axioms AspisR1.JGn_CopyPower08.source
#print axioms AspisR1.JGn_CopyPower12.source
#print axioms AspisR1.JGn_CopyPower16.source
#print axioms AspisR1.JGn_CopyPowers.source
#print axioms AspisR1.JGn_CopyRows.ext
#print axioms AspisR1.JGn_CurrentPreparation.inhabited
#print axioms AspisR1.JGn_ExactPreflight.add
#print axioms AspisR1.JGn_ExactPreflight.product
#print axioms AspisR1.JGn_ExactPreflight.loop
#print axioms AspisR1.JGn_FieldExact.add
#print axioms AspisR1.JGn_FieldExact.mul
#print axioms AspisR1.JGn_FieldExact.sub
#print axioms AspisR1.JGn_FieldExact.bind
#print axioms AspisR1.JGn_FullEven.lane0
#print axioms AspisR1.JGn_FullEven.lane1
#print axioms AspisR1.JGn_FullEven.lane2
#print axioms AspisR1.JGn_FullEven.lane3
#print axioms AspisR1.JGn_FullEven.lane4
#print axioms AspisR1.JGn_FullEven.lane5
#print axioms AspisR1.JGn_FullEven.lane6
#print axioms AspisR1.JGn_FullEven.lane7
#print axioms AspisR1.JGn_FullEven.lane8
#print axioms AspisR1.JGn_FullEven.lane9
#print axioms AspisR1.JGn_FullEven.lane10
#print axioms AspisR1.JGn_FullEven.lane11
#print axioms AspisR1.JGn_FullEven.lane12
#print axioms AspisR1.JGn_FullEven.lane13
#print axioms AspisR1.JGn_FullEven.lane14
#print axioms AspisR1.JGn_FullEven.lane15
#print axioms AspisR1.JGn_FullEven.value
#print axioms AspisR1.JGn_FullFinal.lane0
#print axioms AspisR1.JGn_FullFinal.lane1
#print axioms AspisR1.JGn_FullFinal.lane2
#print axioms AspisR1.JGn_FullFinal.lane3
#print axioms AspisR1.JGn_FullFinal.lane4
#print axioms AspisR1.JGn_FullFinal.lane5
#print axioms AspisR1.JGn_FullFinal.lane6
#print axioms AspisR1.JGn_FullFinal.lane7
#print axioms AspisR1.JGn_FullFinal.lane8
#print axioms AspisR1.JGn_FullFinal.lane9
#print axioms AspisR1.JGn_FullFinal.lane10
#print axioms AspisR1.JGn_FullFinal.lane11
#print axioms AspisR1.JGn_FullFinal.lane12
#print axioms AspisR1.JGn_FullFinal.lane13
#print axioms AspisR1.JGn_FullFinal.lane14
#print axioms AspisR1.JGn_FullFinal.lane15
#print axioms AspisR1.JGn_FullFinal.value
#print axioms AspisR1.JGn_FullMath.value
#print axioms AspisR1.JGn_FullMid.lane0
#print axioms AspisR1.JGn_FullMid.lane1
#print axioms AspisR1.JGn_FullMid.lane2
#print axioms AspisR1.JGn_FullMid.lane3
#print axioms AspisR1.JGn_FullMid.lane4
#print axioms AspisR1.JGn_FullMid.lane5
#print axioms AspisR1.JGn_FullMid.lane6
#print axioms AspisR1.JGn_FullMid.lane7
#print axioms AspisR1.JGn_FullMid.lane8
#print axioms AspisR1.JGn_FullMid.lane9
#print axioms AspisR1.JGn_FullMid.lane10
#print axioms AspisR1.JGn_FullMid.lane11
#print axioms AspisR1.JGn_FullMid.lane12
#print axioms AspisR1.JGn_FullMid.lane13
#print axioms AspisR1.JGn_FullMid.lane14
#print axioms AspisR1.JGn_FullMid.lane15
#print axioms AspisR1.JGn_FullMid.value
#print axioms AspisR1.JGn_FullNumeric.pack
#print axioms AspisR1.JGn_FullNumeric.source
#print axioms AspisR1.JGn_FullOdd.lane0
#print axioms AspisR1.JGn_FullOdd.lane1
#print axioms AspisR1.JGn_FullOdd.lane2
#print axioms AspisR1.JGn_FullOdd.lane3
#print axioms AspisR1.JGn_FullOdd.lane4
#print axioms AspisR1.JGn_FullOdd.lane5
#print axioms AspisR1.JGn_FullOdd.lane6
#print axioms AspisR1.JGn_FullOdd.lane7
#print axioms AspisR1.JGn_FullOdd.lane8
#print axioms AspisR1.JGn_FullOdd.lane9
#print axioms AspisR1.JGn_FullOdd.lane10
#print axioms AspisR1.JGn_FullOdd.lane11
#print axioms AspisR1.JGn_FullOdd.lane12
#print axioms AspisR1.JGn_FullOdd.lane13
#print axioms AspisR1.JGn_FullOdd.lane14
#print axioms AspisR1.JGn_FullOdd.lane15
#print axioms AspisR1.JGn_FullOdd.value
#print axioms AspisR1.JGn_FullPow0.lane0
#print axioms AspisR1.JGn_FullPow0.lane1
#print axioms AspisR1.JGn_FullPow0.lane2
#print axioms AspisR1.JGn_FullPow0.lane3
#print axioms AspisR1.JGn_FullPow0.lane4
#print axioms AspisR1.JGn_FullPow0.lane5
#print axioms AspisR1.JGn_FullPow0.lane6
#print axioms AspisR1.JGn_FullPow0.lane7
#print axioms AspisR1.JGn_FullPow0.lane8
#print axioms AspisR1.JGn_FullPow0.lane9
#print axioms AspisR1.JGn_FullPow0.lane10
#print axioms AspisR1.JGn_FullPow0.lane11
#print axioms AspisR1.JGn_FullPow0.lane12
#print axioms AspisR1.JGn_FullPow0.lane13
#print axioms AspisR1.JGn_FullPow0.lane14
#print axioms AspisR1.JGn_FullPow0.lane15
#print axioms AspisR1.JGn_FullPow0.value
#print axioms AspisR1.JGn_FullPow1.lane0
#print axioms AspisR1.JGn_FullPow1.lane1
#print axioms AspisR1.JGn_FullPow1.lane2
#print axioms AspisR1.JGn_FullPow1.lane3
#print axioms AspisR1.JGn_FullPow1.lane4
#print axioms AspisR1.JGn_FullPow1.lane5
#print axioms AspisR1.JGn_FullPow1.lane6
#print axioms AspisR1.JGn_FullPow1.lane7
#print axioms AspisR1.JGn_FullPow1.lane8
#print axioms AspisR1.JGn_FullPow1.lane9
#print axioms AspisR1.JGn_FullPow1.lane10
#print axioms AspisR1.JGn_FullPow1.lane11
#print axioms AspisR1.JGn_FullPow1.lane12
#print axioms AspisR1.JGn_FullPow1.lane13
#print axioms AspisR1.JGn_FullPow1.lane14
#print axioms AspisR1.JGn_FullPow1.lane15
#print axioms AspisR1.JGn_FullPow1.value
#print axioms AspisR1.JGn_LeadingNumeric.pack
#print axioms AspisR1.JGn_LeadingNumeric.source
#print axioms AspisR1.JGn_MaskedAcceptance.source
#print axioms AspisR1.JGn_MaskedAcceptance.formula
#print axioms AspisR1.JGn_PatternMath.lane0
#print axioms AspisR1.JGn_PatternMath.lane1
#print axioms AspisR1.JGn_PatternMath.lane2
#print axioms AspisR1.JGn_PatternMath.lane3
#print axioms AspisR1.JGn_PatternMath.lane4
#print axioms AspisR1.JGn_PatternMath.lane5
#print axioms AspisR1.JGn_PatternMath.lane6
#print axioms AspisR1.JGn_PatternMath.lane7
#print axioms AspisR1.JGn_PatternMath.lane8
#print axioms AspisR1.JGn_PatternMath.lane9
#print axioms AspisR1.JGn_PatternMath.lane10
#print axioms AspisR1.JGn_PatternMath.lane11
#print axioms AspisR1.JGn_PatternMath.lane12
#print axioms AspisR1.JGn_PatternMath.lane13
#print axioms AspisR1.JGn_PatternMath.value
#print axioms AspisR1.JGn_PoseidonNumeric.model
#print axioms AspisR1.JGn_PoseidonNumeric.identified
#print axioms AspisR1.JGn_PrefixEval.bind_continue
#print axioms AspisR1.JGn_PrefixPreflight.source
#print axioms AspisR1.JGn_PrepareBuffer.length
#print axioms AspisR1.JGn_PrepareBuffer.take
#print axioms AspisR1.JGn_PrepareBuffer.drop
#print axioms AspisR1.JGn_PrepareBuffer.split
#print axioms AspisR1.JGn_PrepareBuffer.recombine
#print axioms AspisR1.JGn_SelectedHelper.value
#print axioms AspisR1.JGn_SplitSource.source
#print axioms AspisR1.JGn_TerminalArithmetic.composition
#print axioms AspisR1.JGn_TerminalArithmetic.terminal
#print axioms AspisR1.JGn_TerminalEquality.tail5
#print axioms AspisR1.JGn_TerminalEquality.weight
#print axioms AspisR1.JGn_TerminalIdentified.source
#print axioms AspisR1.JGn_TerminalIdentified.identified
#print axioms AspisR1.JGn_TerminalLow.sem16
#print axioms AspisR1.JGn_TerminalLow.sem08
#print axioms AspisR1.JGn_TerminalLow.sem00
#print axioms AspisR1.JGn_TerminalLow.poseidon
#print axioms AspisR1.JGn_TerminalPowers.four
#print axioms AspisR1.JGn_TerminalPowers.twentyEight
#print AspisR1.JGn_TerminalIdentified.identified
#print AspisR1.JGn_MaskedAcceptance.source
#print AspisR1.JGn_CurrentPreparation.inhabited
#print AspisR1.JGn_TX1Prefix.inhabited
#print AspisR1.ARX_Root.deployed
#print axioms AspisR1.ARX_Root.deployed
