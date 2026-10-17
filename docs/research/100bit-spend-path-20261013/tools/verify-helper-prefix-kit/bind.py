from pathlib import Path
import json,hashlib,re,argparse
R=Path(__file__).resolve().parents[5];B=R/'docs/research/100bit-spend-path-20261013';K=B/'tools/verify-helper-prefix-kit';O=B/'lean/bridge-verify-prefix-fe80-20261017';O.mkdir(exist_ok=True)
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
def emit(p,text):
 if args.check:assert p.read_text()==text,p
 else:p.write_text(text)
s={};p=B/'tools/tx1-caller-extraction-kit/union.py';s['__file__']=str(p);exec(p.read_text().split('p=argparse.ArgumentParser()',1)[0],s);chunks=s['chunks'];tok=s['a'].tokens;sha=lambda b:hashlib.sha256(b).hexdigest()
base=(B/'lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean').read_bytes();rawdir=B/'evidence/verify-helper-prefix-fe80-20261017/generated/AspisR1PublicPreparation';old=chunks(base);new=chunks((rawdir/'Types.lean').read_bytes());audit=[]
for n,v in new.items():
 assert n in old,n
 normal=[]
 body=v.replace('Self → (Slice (Slice Std.U8))','Self → Slice (Slice Std.U8)')
 if body!=v:normal.append('remove redundant argument parentheses')
 if body.startswith('@[discriminant isize]\n') and not old[n].startswith('@[discriminant isize]\n'):body=body.removeprefix('@[discriminant isize]\n');normal.append('reuse existing canonical named discriminant reader/instance; remove raw deriving attribute only')
 assert tok(body)==tok(old[n]),n
 audit.append({'declaration':n,'normalizations':normal,'raw_sha256':sha(v.encode()),'canonical_token_sha256':sha(json.dumps(tok(body),separators=(',',':')).encode())})
source=(B/'lean/ExtractedDigest32PrefixAdapter.lean').read_text();core=source[:source.index('\ndef completedRecords')];core=core.replace('import ExtractedPrefixTypedFull','import AspisR1PrefixAggregateParser.Funs');core+='\n#print axioms parseAccepted\n#print axioms parse_success\nend AspisR1PublicPreparation.PrefixAdapter\n';emit(O/'ExtractedPrefixParseCore.lean',core)
raw=(rawdir/'Funs.lean').read_bytes();ds=chunks(raw);mp={'r1_semantic.mark':'VerifyPrefix.mark','r1_semantic.verify_observed':'VerifyPrefix.verify','r1_wire.Prefix.parse':'PrefixAdapter.parseAccepted','r1_semantic.verify_finish':'F'};pat=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])' for n in sorted(mp,key=len,reverse=True)))
header='''import ExtractedPrefixParseCore
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1PublicPreparation
abbrev VerifyPrefix.Finish := {H : Type} → aspis_core.Digest32 H →
  pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix →
  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (verifier.Phase → Result Unit) →
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
'''
outs=[];bindings=[]
for n in ['r1_semantic.mark','r1_semantic.verify_observed']:
 body=pat.sub(lambda m:mp[m[0]],ds[n]);extra=''
 if n.endswith('verify_observed'):
  extra=' (F : VerifyPrefix.Finish)';body=body.replace('def VerifyPrefix.verify\n','def VerifyPrefix.verify'+extra+'\n',1)
 outs.append(body);bindings.append({'declaration':n,'source_token_sha256':sha(json.dumps(tok(ds[n]),separators=(',',':')).encode()),'raw_body_sha256':sha(ds[n].encode()),'model_sha256':sha(body.encode()),'binder_addition':extra})
model=header+'\n'.join(outs)+'\n#print axioms VerifyPrefix.mark\n#print axioms VerifyPrefix.verify\nend AspisR1PublicPreparation\n';emit(O/'ExtractedVerifyPrefixModel.lean',model)
record={'revision':'fe80a544afce3024cbc9e5be765c1d05ab785d56','canonical_types_sha256':sha(base),'base_types_sha256':sha(base),'shared_types_sha256':sha(base),'shared_funs_sha256':sha((B/'lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Funs.lean').read_bytes()),'new_types':[],'raw_types_sha256':sha((rawdir/'Types.lean').read_bytes()),'common_type_audit':audit,'raw_funs_sha256':sha(raw),'identifier_map':mp,'exact_body_audits':bindings,'model_sha256':sha(model.encode()),'parser_adapter_source_sha256':sha(source.encode()),'parser_core_sha256':sha(core.encode()),'excluded_templates':['FunsExternal_Template.lean'],'scope':'Complete actual verify_observed under r0/private-leaf-salts. Parser fixed to accepted actual parser with nominal carriers mapped; public_transcript/begin fixed to canonical actual functions. Only complete verify_finish API universally parameterized. No staging body or global axiom imported.'};emit(O/'binding-audit.json',json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps({'check':args.check,'model_sha256':sha(model.encode()),'common_types':len(audit),'exact_bound_bodies':len(bindings)}))
