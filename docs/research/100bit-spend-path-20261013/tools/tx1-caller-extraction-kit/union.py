#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,shutil
R=Path(__file__).resolve().parents[5];B=R/'docs/research/100bit-spend-path-20261013';sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('audit',B/'tools/public-binding-followup-kit/bridge-callers.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
def chunks(raw):
 text=a.uncomment(raw.decode());pat=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:def|structure|inductive|abbrev|instance)\s+(\S+)',re.M);ms=list(pat.finditer(text));out={}
 for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else text.rfind('\nend ');out[m[1]]=re.sub(r'\s*@\[[^\]]*\]\s*$','',text[m.start():end]).strip()+'\n'
 return out
p=argparse.ArgumentParser();p.add_argument('--base',type=Path,required=True);p.add_argument('--generated',type=Path,required=True);p.add_argument('--out',type=Path,required=True);x=p.parse_args()
base=(x.base/'AspisR1PublicPreparation/Types.lean').read_bytes();raw=(x.generated/'Types.lean').read_bytes();old=chunks(base);new=chunks(raw);audit=[]
for n in sorted(set(old)&set(new)):
 body=new[n];changes=[]
 if n=='aspis_core.Digest32':
  adapted=body.replace('Self → (Slice (Slice Std.U8))','Self → Slice (Slice Std.U8)')
  if adapted!=body:changes.append('remove redundant argument parentheses');body=adapted
 if body.startswith('@[discriminant isize]\n') and not old[n].startswith('@[discriminant isize]\n'):
  assert n+'.read_discriminant' in old,n;body=body.removeprefix('@[discriminant isize]\n');changes.append('reuse existing canonical named discriminant reader/instance; remove raw deriving attribute only')
 assert a.tokens(old[n])==a.tokens(body),(n,'changed common type')
 audit.append({'declaration':n,'raw_sha256':sha(new[n].encode()),'canonical_token_sha256':sha(json.dumps(a.tokens(body),separators=(',',':')).encode()),'normalizations':changes})
add=[n for n in new if n not in old];text=base.decode();at=text.rfind('\nend AspisR1PublicPreparation');text=text[:at]+'\n/-! Exact newly emitted tx1 carrier declarations. -/\n'+'\n'.join(new[n] for n in add)+text[at:]
x.out.mkdir(parents=True,exist_ok=True);d=x.out/'AspisR1PublicPreparation';d.mkdir(exist_ok=True);(d/'Types.lean').write_text(text);shutil.copy2(x.base/'AspisR1PublicPreparation/Funs.lean',d/'Funs.lean');shutil.copy2(x.base/'ExtractedPreparedModel.lean',x.out/'ExtractedPreparedModel.lean')
record={'source_revision':'e5c186ba3bcbbf9a0cc5878077aa8848853a65cc','base_types_sha256':sha(base),'raw_types_sha256':sha(raw),'common_type_audit':audit,'new_types':add,'shared_types_sha256':sha(text.encode()),'shared_funs_sha256':sha((d/'Funs.lean').read_bytes()),'rule':'Retain all canonical A declarations exactly; append only new tx1 carrier declarations; common types token-equal after listed existing naming-only normalizations. No carrier function/substitution or foreign axiom.'};(x.out/'union-pins.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps(record))
