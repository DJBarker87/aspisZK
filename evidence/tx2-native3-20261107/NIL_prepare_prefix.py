from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent
fresh=Path('evidence/tx2-native2-20261107/NID_ResumeEmissionFuns.lean').read_text()
cohort=subprocess.check_output(['git','show','HEAD:docs/research/100bit-spend-path-20261013/lean/Stage2ContinuationResumeBody.lean'],text=True)
def prefix(text,definition):
 a=text.index('  := do',text.index(definition));z=text.index('                    let (state, r) ←',a)
 return text[a:z]+'                    next end1 i4\n'
f=prefix(fresh,'def verifier.resume\n')
f=f.replace('NID_call_17','(fun v=>CheckpointBytes4Ops.checkpointSize (variant v))').replace('NID_call_19','(fun v=>CheckpointBytes4Ops.tag (variant v))').replace('NID_call_0','CheckpointBytes4Ops.ne').replace('NID_call_1','CheckpointBytes4Ops.eq').replace('NID_call_3','NIL_FreshOps.any')
f=f.replace('(Slice.Insts.CoreCmpPartialEqArray CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq)','(NID_ResumeEmission.Slice.Insts.CoreCmpPartialEqArray CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq)')
c=prefix(cohort,'def verifier.resumeWithOps\n')
fheader='''def fresh {A H : Type} (aspis_coredigestDigest32Inst : NID_ResumeEmission.aspis_core.digest.Digest32 H)
  (bytes proof public1 : Slice U8) (v : Fresh.V) (hash : H)
  (next : Usize → U8 → Result (core.result.Result A Fresh.Err)) :
  Result (core.result.Result A Fresh.Err)
'''
cheader='''def cohort {A H : Type} (ops : AspisR1Stage2.ResumeOps)
  (aspis_coredigestDigest32Inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
  (bytes proof public1 : Slice U8) (v : Cohort.V) (hash : H)
  (next : Usize → U8 → Result (core.result.Result A Cohort.Err)) :
  Result (core.result.Result A Cohort.Err)
'''
out='''import NIL_HeaderAny
import NIL_TryTransport
import Port6CK_Header
set_option autoImplicit false
noncomputable section
namespace NIL_ResumePrefixCut
open Aeneas Aeneas.Std Result ControlFlow Error NIL_Carriers AspisR1
open NID_ResumeEmission in
'''+fheader+f+'\nopen AspisR1Stage2 in\n'+cheader+c+'''\nend NIL_ResumePrefixCut
'''
(E/'NIL_ResumePrefixCut.lean').write_text(out)
(E/'NIL_PREFIX_PROVENANCE.json').write_text(json.dumps({'fresh_input':'evidence/tx2-native2-20261107/NID_ResumeEmissionFuns.lean','fresh_sha256':hashlib.sha256(fresh.encode()).hexdigest(),'cohort_input':'Stage2ContinuationResumeBody.lean','cohort_sha256':hashlib.sha256(cohort.encode()).hexdigest(),'cut':'before first raw reader, continuation arguments are exactly checksum end1 and source header i4','changes':'literal prefix specialization of opaque equality/header/size/tag parameters; digest and input carriers preserved; no callee law assumed'},indent=2)+'\n')
