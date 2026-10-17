#!/usr/bin/env python3
"""Whole query binder using canonical shared carriers, no imported externals."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;BASE=R/'docs/research/100bit-spend-path-20261013';sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('binder',BASE/'tools/prepared-actual-extraction-kit/bind.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
p=argparse.ArgumentParser();p.add_argument('--generated',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');x=p.parse_args()
prior=BASE/'lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation';raw={n:(x.generated/n).read_bytes()for n in ['Types.lean','Funs.lean']};current={n:a.chunks(raw[n])for n in raw};audit={}
for n in raw:
 old=a.chunks((prior/n).read_bytes());shared=set(old)&set(current[n]);items=[]
 for name in sorted(shared):
  text=current[n][name]
  if name=='aspis_core.Digest32':text=text.replace('Self → (Slice (Slice Std.U8))','Self → Slice (Slice Std.U8)')
  assert a.a.tokens(text)==a.a.tokens(old[name]),(n,name)
  items.append({'declaration':name,'prior_token_sha256':sha(json.dumps(a.a.tokens(old[name])).encode()),'current_token_sha256':sha(json.dumps(a.a.tokens(text)).encode()),'statement_diff':''})
 audit[n]={'common_declarations':items,'prior_source_sha256':sha((prior/n).read_bytes()),'raw_current_sha256':sha(raw[n])}
newtypes=[current['Types.lean'][n]for n in ['aspis_core.transcript.QuerySampleError','transcript.Transcript.queries.closure']]
helpers=[n for n in current['Funs.lean']if n.startswith('transcript.Transcript.queries.closure.')]
assert len(helpers)==2
names=['transcript.Transcript.queries','queries_entry'];mappings={'transcript.Transcript.queries':'QueriesModel.queries B','queries_entry':'QueriesModel.entry B','aspis_core.r0_transcript.queries_from_pairs':'B.decode','aspis_core.field.WideExact.from_m31':'B.embed'};defs=[];bodyaudit=[]
for name in names:
 original=current['Funs.lean'][name];pat=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])'for n in sorted(mappings,key=len,reverse=True)));counts={n:len(re.findall(re.escape(n)+r'(?![A-Za-z0-9_.])',original))for n in mappings};text=pat.sub(lambda m:mappings[m[0]],original);target=mappings[name];assert text.startswith('def '+target+'\n');text=text.replace('def '+target+'\n','def '+target.removesuffix(' B')+' (B : QueriesModel.Boundaries)\n',1);defs.append(text);bodyaudit.append({'source_declaration':name,'source_token_sha256':sha(json.dumps(a.a.tokens(original)).encode()),'adapted_sha256':sha(text.encode()),'identifier_replacement_counts':{n:c for n,c in counts.items()if c},'sole_other_change':'Insert explicit Boundaries parameter after new definition name'})
text='''import AspisR1PublicPreparation.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1PublicPreparation
'''+ '\n'.join(newtypes)+'''\nstructure QueriesModel.Boundaries where
  decode : Array (Array U8 32#usize) 8#usize → Array (Array U8 32#usize) 8#usize →
    Result (core.result.Result (Array U32 22#usize × Array U8 32#usize) aspis_core.transcript.QuerySampleError)
  embed : aspis_core.field.M31 → Result aspis_core.field.WideExact
'''+ '\n'.join(current['Funs.lean'][n]for n in helpers)+'\n'+'\n'.join(defs)+'\n#print axioms QueriesModel.queries\n#print axioms QueriesModel.entry\nend AspisR1PublicPreparation\n'
assert not re.search(r'^\s*(axiom|opaque)\b',text,re.M)
pins={'source_revision':'1b98d3cf35fb1959da75bcec0a396f182d4b1f3d','rule':'New QuerySampleError/closure and helpers emitted exactly inside model; all shared canonical carriers/common functions token-identical after explicit Digest32 redundant-parentheses removal. Entire query/entry bodies bound by listed exact identifier substitutions +explicit parameter only. External template not imported.','common_carrier_audit':audit,'model_body_audit':bodyaudit,'output_sha256':sha(text.encode())}
outputs={'ExtractedOpeningQueriesModel.lean':text.encode(),'binding-pins.json':(json.dumps(pins,indent=2)+'\n').encode()}
for n,b in outputs.items():
 q=x.out/n
 if x.check:assert q.read_bytes()==b,n
 else:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
print(json.dumps({'status':'PASS','model_sha256':sha(text.encode()),'checked':x.check}))
