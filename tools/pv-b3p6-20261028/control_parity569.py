"""Pin the exact standard-library bodies consumed by the local control laws."""
from pathlib import Path
import json,lzma,re,hashlib
R=Path('evidence/pv-b3p6-20261028/resume18')
items=[('ops/index_range.rs','fn try_fold','PV_B3P_IndexRangeFormatting569227.handler_independent'),('ops/index_range.rs','unsafe fn next_unchecked','PV_B3P_PreconditionFormatting569227.index_range_conditions'),('array/mod.rs','fn try_from_fn_erased','PV_B3P_InitializerFormatting569227.loop_independent'),('array/mod.rs','unsafe fn push_unchecked','PV_B3P_PreconditionFormatting569227.initializer_checks'),('slice/iter/macros.rs','fn next(','PV_B3P_PreconditionFormatting569227.slice_subtraction_check')]
def get(ver,path,needle):
 p=R/('std569-source'if path in ['ops/index_range.rs','slice/iter/macros.rs']else 'std559-source')/ver/(path+'.xz');data=lzma.decompress(p.read_bytes());s=data.decode();a=s.index(needle);b=s.index('{',a);d=1;i=b+1
 while d:
  d+=(s[i]=='{')-(s[i]=='}');i+=1
 return dict(source=str(p),source_sha256=hashlib.sha256(data).hexdigest(),body=s[b:i],body_sha256=hashlib.sha256(s[b:i].encode()).hexdigest())
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
rows=[]
for path,needle,law in items:
 old=get('1.94.1',path,needle);new=get('nightly-2026-06-01',path,needle);assert tok(old['body'])==tok(new['body'])
 rows.append(dict(item=needle,path=path,deployed=old,extractor=new,body_tokens_identical=True,local_control_law=law,signature_and_carrier_association='not inferred from body parity',pointer_drop_and_caller_association='OPEN'))
g=json.loads((R/'imports-b3q/pv-b3q2-20261031/direct3-instantiated-callcone.json').read_text())
initializers=[dict(instance=k,environment=v['environment'],body_law='PV_B3P_InitializerFormatting569227.loop_independent',scope='same exact generic source numeric control; no concrete buffer/restoration/drop association')for k,v in g['instances'].items()if v['id']==370];assert len(initializers)==16
(R/'CONTROL-SOURCE-PARITY-D569.json').write_text(json.dumps(dict(body_comparisons=rows,initializer_instances=initializers,credit='STRUCTURAL source-body parity plus named local Lean laws; no whole-source/dictionary result',qualifications=['own-1','b3p6-1 fifth-amendment tool-trust reclassification','ae1-2','V370 compiler cohort retained','fmt-1(a) full event certificate OPEN','rdea-2 world/failure obligations retained']),indent=2)+'\n');print('five body comparisons and sixteen initializer instantiations recorded')
