#!/usr/bin/env python3
"""Exact complete emitted finish/circle bodies; checked actual rounds fixed."""
from pathlib import Path
import argparse,hashlib,json,re
R=Path(__file__).resolve().parents[5];B=R/'docs/research/100bit-spend-path-20261013';s={'__file__':str(B/'tools/tx1-caller-extraction-kit/union.py')};exec((B/'tools/tx1-caller-extraction-kit/union.py').read_text().split('p=argparse.ArgumentParser()',1)[0],s);tokens=s['a'].tokens
def chunks(raw):
 text=s['a'].uncomment(raw.decode());pat=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:def|impl_def|structure|inductive|abbrev|instance)\s+(\S+)',re.M);ms=list(pat.finditer(text));out={}
 for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else text.rfind('\nend ');out[m[1]]=re.sub(r'\s*@\[[^\]]*\]\s*$','',text[m.start():end]).strip()+'\n'
 return out
sha=lambda b:hashlib.sha256(b).hexdigest();ap=argparse.ArgumentParser();ap.add_argument('--generated',type=Path,required=True);ap.add_argument('--round-model',type=Path,required=True);ap.add_argument('--round-generated',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args();raw=(a.generated/'Funs.lean').read_bytes();F=chunks(raw);T=chunks((a.generated/'Types.lean').read_bytes());C=chunks((B/'lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean').read_bytes());audit=[]
for n in set(T)&set(C):
 body=T[n];norm=[]
 x=body.replace('Self → (Slice (Slice Std.U8))','Self → Slice (Slice Std.U8)')
 if x!=body:norm.append('remove redundant argument parentheses');body=x
 if body.startswith('@[discriminant isize]\n') and not C[n].startswith('@[discriminant isize]\n'):body=body.removeprefix('@[discriminant isize]\n');norm.append('reuse existing canonical named discriminant reader/instance; remove raw deriving attribute only')
 assert tokens(body)==tokens(C[n]),n;audit.append({'declaration':n,'normalizations':norm,'raw_sha256':sha(T[n].encode()),'canonical_token_sha256':sha(json.dumps(tokens(body),separators=(',',':')).encode())})
CF=chunks((B/'lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Funs.lean').read_bytes());functionaudit=[]
for n in ['core.result.Result.map_err','r1_wire.ValidatedRecord.impl.row','r1_wire.ValidatedRecord.impl.framed','r1_wire.Prefix.record','r1_wire.Prefix.validated_record','r1_wire.SemanticTranscript.impl.state','r1_wire.SemanticTranscript.sample_block_validated']:
 assert tokens(F[n])==tokens(CF[n]),n
 functionaudit.append({'declaration':n,'raw_and_canonical_token_sha256':sha(json.dumps(tokens(F[n]),separators=(',',':')).encode())})
RG=chunks((a.round_generated/'Funs.lean').read_bytes());roundaudit=[]
for n in ['aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq','aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq','aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31','r1_semantic.semantic_round','r1_semantic.semantic_rounds']:
 assert tokens(F[n])==tokens(RG[n]),n
 roundaudit.append({'declaration':n,'finish_and_accepted_rounds_token_sha256':sha(json.dumps(tokens(F[n]),separators=(',',':')).encode())})
selected=['r1_wire.Prefix.payload','aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq','r1_wire.SemanticTranscript.circle_validated']+[n for n in F if n.startswith('r1_semantic.verify_finish.closure')]+['r1_semantic.verify_finish']
mp={'r1_wire.Prefix.payload':'FinishModel.payload','sampler.CircleRow.First':'FinishModel.CircleRow.First','sampler.CircleRow.Second':'FinishModel.CircleRow.Second','sampler.CircleRow':'FinishModel.CircleRow','r1_semantic.verify_finish.closure_2':'FinishModel.Closure2','r1_semantic.verify_finish.closure_1':'FinishModel.Closure1','r1_semantic.verify_finish.closure':'FinishModel.Closure','r1_semantic.semantic_rounds':'RoundModel.rounds R','r1_semantic.mark':'VerifyPrefix.mark','core.array.from_fn':'B.fromFn','aspis_core.state_only_hiding.state_only_selected_mask_value':'B.mask','aspis_core.field.QM31.add':'B.add','aspis_core.field.QM31.mul':'B.mul','pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31':'B.terminal','r1_wire.ValidatedRecord.decode_k':'R.decode','sampler.circle_sample':'B.circle','r1_semantic.claims':'B.claims','r1_wire.SemanticTranscript.circle_validated':'FinishModel.circle_validated B','aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq':'FinishModel.pointEq','aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint':'FinishModel.pointInst','r1_semantic.verify_finish':'FinishModel.finish R B'}
unwrap_callee=re.search(r'core\.result\.Result\.unwrap\s+core\.fmt\.DebugTryFromSliceError',F['r1_semantic.verify_finish']);assert unwrap_callee is not None;mp[unwrap_callee[0]]='B.unwrapRoot'
for i,n in enumerate(selected):
 if n.startswith('r1_semantic.verify_finish.closure'):mp[n]='FinishModel.closureFn'+str(i-1)
pat=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])' for n in sorted(mp,key=len,reverse=True)));sub=lambda body:pat.sub(lambda m:mp[m[0]],body)
newtypes=[]
for n in T:
 if n in C:continue
 assert n in mp,n
 body=sub(T[n])
 if n=='sampler.CircleRow':
  body=body.removeprefix('@[discriminant isize]\n');body+='\ndef FinishModel.CircleRow.read_discriminant : FinishModel.CircleRow → Isize\n  | .First => 0#isize\n  | .Second => 1#isize\ninstance _root_.AspisR1PublicPreparation.FinishModel.CircleRow.instDiscriminant :\n    Aeneas.Std.Discriminant FinishModel.CircleRow Isize where\n  read_discriminant := FinishModel.CircleRow.read_discriminant\n'
 newtypes.append(body)
head='''import ExtractedSemanticRoundsModel
import ExtractedVerifyPrefixModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1PublicPreparation
'''
head+='\n'.join(newtypes)+'''
structure FinishModel.Boundaries where
  fromFn : {T F : Type} → (N : Usize) → core.ops.function.FnMut F Usize T → F → Result (Array T N)
  mask : Array aspis_core.field.QM31 16#usize → Array aspis_core.field.QM31 10#usize →
    aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize → Result aspis_core.field.QM31
  add : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
  mul : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
  terminal : pool_v1.pair_forest_semantic_terminal.r0.Public →
    Array (Array aspis_core.field.QM31 29#usize) 3#usize → Array aspis_core.field.QM31 10#usize →
    r1_wire.Challenges → Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
  circle : Array U8 32#usize → FinishModel.CircleRow → Result aspis_core.circle.SecureCirclePoint
  unwrapRoot : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError → Result (Array U8 32#usize)
  claims : r1_wire.Prefix → Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize) 3#usize) r1_wire.Error)
'''
defs=[];ba=[]
for n in selected:
 body=sub(F[n]);binder=''
 if n=='r1_wire.SemanticTranscript.circle_validated':binder=' (B : FinishModel.Boundaries)'
 if n=='r1_semantic.verify_finish':binder=' (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)'
 if binder:
  key='def '+mp[n]+'\n';assert key in body,(n,body[:120]);body=body.replace(key,'def '+mp[n].split(' ')[0]+binder+'\n',1)
 defs.append(body);ba.append({'declaration':n,'source_token_sha256':sha(json.dumps(tokens(F[n]),separators=(',',':')).encode()),'model_sha256':sha(body.encode()),'binder_addition':binder,'root_unwrap_substitution':n=='r1_semantic.verify_finish'})
model=head+'\n'.join(defs)+'\n'+''.join('#print axioms '+mp[n].split(' ')[0]+'\n' for n in selected)+'end AspisR1PublicPreparation\n';assert not re.search(r'^\s*(axiom|opaque)\b',model,re.M) and 'FunsExternal' not in model
record={'chunk_parser':'include_impl_def','source_revision':'a555 final approved1f','raw_funs_sha256':sha(raw),'raw_types_sha256':sha((a.generated/'Types.lean').read_bytes()),'identifier_map':mp,'exact_body_audits':ba,'model_sha256':sha(model.encode()),'canonical_common_types':sorted(audit,key=lambda v:v['declaration']),'canonical_function_token_identity':functionaudit,'fixed_round_body_token_identity':roundaudit,'accepted_rounds_raw_funs_sha256':sha((a.round_generated/'Funs.lean').read_bytes()),'new_nominal_types':[n for n in T if n not in C],'fixed_actual_round_model_source_sha256':sha(a.round_model.read_bytes()),'scope':'Complete actual emitted verify_finish/circle_validated and source closures. Actual RoundModel.rounds fixed with same R.decode; actual Prefix/getter/digest/equality definitions reused. Eight arithmetic/allocation/circle/root-unwrap interpretation APIs explicit, no foreign axiom or staging semantics.'};a.out.mkdir(parents=True,exist_ok=True)
for p,data in [(a.out/'ExtractedVerifyFinishModel.lean',model.encode()),(a.out/'binding-audit.json',(json.dumps(record,indent=2,sort_keys=True)+'\n').encode())]:
 if a.check:assert p.read_bytes()==data
 else:p.write_bytes(data)
print(json.dumps({'model_sha256':record['model_sha256'],'exact_bodies':len(selected),'new_nominal_types':record['new_nominal_types']}))
