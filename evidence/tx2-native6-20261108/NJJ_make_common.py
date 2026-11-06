from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent
src=subprocess.check_output(['git','show','2e0207c411953c915ab02fad625f33a94a865671:evidence/tx2-model2-20261106/NHT_EmittedCommon.lean'],text=True)
assert hashlib.sha256(src.encode()).hexdigest()=='c70bbe12808b3549a9014a095565dc69d088d92e36baacc9c7e59204b2cc9876','STOP model input drift'
header='''import NJJ_QueryOps
import NJC_FilledClause
set_option autoImplicit false
noncomputable section
namespace NJJ_Common
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
abbrev Merkle := ∀ {H : Type}, aspis_core.digest.Digest32 H → Slice U8 → verifier.Prepared → Array U8 32#usize → Usize → H → Result (core.result.Result Unit verifier.Error)
abbrev Finish := verifier.View → verifier.Prepared → verifier.Accumulator → Option (verifier.Phase → Result Unit) → Result (core.result.Result Unit verifier.Error)

def resume (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8)
 (v : transport.Variant) (hash : H) :=
 NHT_ResultPort.action (NJC_ResumeCalls.reference (NJC_FilledClause.reserved reservation) d ck proof pub v hash)
def pending (reservation : NP6_StdModel.Reservation) :=
 Port3_NativePendingInstall.source (NJC_FilledClause.reserved reservation)
def query := NHT_PacketOps.query NJJ_QueryOps.concrete 0 0

/-- Dictionary-free source-model candidate. The two named sibling functions
are explicitly OPEN. The Reservation arguments are not yet attached to actual
allocator events and therefore FAIL (aq)(2)/(au)(5); no native root is claimed.
See NJJ_AllocatorSites.md. This body is a mechanical substitution in the pinned
NHT emitted common body, with all standard calls left literally in place. -/
'''
body=src[src.index('def tx2_common'):src.rindex('end NHT_EmittedCommon')]
body=body.replace('def tx2_common (ops : VTop_Stages.Ops)','def run (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)')
sub={'op18':'(resume weightReservation)','op17':'NHT_PacketOps.powers','op13':'NHV_ReleaseOps.mark','op2':'NJC_ClosedCalls.inactive','op5':'merkle','op11':'NJC_ClosedCalls.geometry','op10':'(pending rawReservation)','op6':'query','op9':'Port3_FlushInstall.flush','op19':'finish'}
body=re.sub(r'ops\.(op\d+)\b',lambda m:sub[m[1]],body)
assert not re.search(r'(?<![.\w])ops\.',body)
tail='''
def install (unused : VTop_Stages.Ops)
 (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish) : VTop_Stages.Ops :=
 {unused with
 op18:=resume weightReservation,op17:=NHT_PacketOps.powers,op13:=NHV_ReleaseOps.mark,
 op2:=NJC_ClosedCalls.inactive,op5:=merkle,op11:=NJC_ClosedCalls.geometry,
 op10:=pending rawReservation,op6:=query,op9:=Port3_FlushInstall.flush,op19:=finish}

/-- Auxiliary mechanical specialization of the emitted body. `unused` is
absent from run; this is not a positive-root theorem under (aq)(2). -/
theorem source (unused : VTop_Stages.Ops)
 (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NHT_EmittedCommon.tx2_common (install unused weightReservation rawReservation merkle finish) d pub proof ck hash none=
 run weightReservation rawReservation merkle finish d pub proof ck hash none := by rfl

#print axioms source
#print source
#print run
end NJJ_Common
'''
(E/'NJJ_Common.lean').write_text(header+body+tail)
(E/'NJJ_COMMON_TRANSFORM.json').write_text(json.dumps(dict(input='evidence/tx2-model2-20261106/NHT_EmittedCommon.lean',input_sha256=hashlib.sha256(src.encode()).hexdigest(),substitutions=sub,source_change=False,positive_native_root=False),indent=2)+'\n')
