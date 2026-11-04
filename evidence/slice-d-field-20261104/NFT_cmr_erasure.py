from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
src=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-core/src/state_only_hiding.rs'],text=True)
code=json.loads((E/'NFT_NATIVE_INPUTS.json').read_text())['crates/aspis-core/src/NFT_cmr.rs']
original=re.search(r'fn cm31_mul_r\(value: CM31\) -> CM31 \{(.*?)\n\}',src,re.S)[1]
logged=re.search(r'fn logged\(value:CM31,log:&mut Log\)->CM31\{(.*?)\}',code,re.S)[1]
parts=logged.split(';');expr=parts[-1]
bindings={}
for part in parts[:-1]:
 m=re.fullmatch(r'let (aa|real|bb|imag)=(.*)',part);assert m,part
 value=m[2]
 for k,v in bindings.items():value=re.sub(r'\b'+k+r'\b','('+v+')',value)
 bindings[m[1]]=value
for k,v in reversed(list(bindings.items())):expr=re.sub(r'\b'+k+r'\b','('+v+')',expr)
expected='CM31::new(value.a.double().sub(value.b),value.a.add(value.b.double()))'
# Explicit ANF expansion checks each of the four child sites and their order.
assert parts[:-1]==['let aa=op(log,0,value.a,M31(0))','let real=op(log,1,aa,value.b)','let bb=op(log,2,value.b,M31(0))','let imag=op(log,3,value.a,bb)']
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize(original)==expected
assert parts[-1]=='CM31::new(real,imag)'
(E/'NFT_CMR_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_body_sha256=hashlib.sha256(original.encode()).hexdigest(),logged_body_sha256=hashlib.sha256(logged.encode()).hexdigest(),erasure_equal=True,ANF_child_order=['a.double','aa.sub(b)','b.double','a.add(bb)'],exact_original_expression=expected,native=['NFT_K059','NFT_K060'],model='NFT_Cmr.source',value='NFQ_Linear.source',method='opaque local-record call log; no direct product-value Kani certificate'),indent=1)+'\n');print('PASS exact four-site ANF erasure')
