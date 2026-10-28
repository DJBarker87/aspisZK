"""Exact declaration partition after the monolithic memory-review stop."""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');p=D/'ported227-shared-resume5.lean.txt';s=p.read_text();canonical=s.split('\n#print axioms ')[0];canonical=re.sub(r'\nend PV_B3P_227\s*$','',canonical)
bs=re.split(r'(?=^/-- \[)',canonical,flags=re.M);header=bs[0];decls=bs[1:];names=[]
for b in decls:
 m=re.search(r'^def\s+(\S+)',b,re.M);assert m,b[:150];names.append(m[1])
assert len(names)==186,len(names)
cuts=[0,5,14,25,32,39,40,41,42,43,49,52,56,57,64,70,79,82,85,92,95,96,97,100,103,104,105,106,107,108,109,110,112,114,118,121,122,126,136,143,147,150,154,160,164,166,170,176,183,185]
old_names=re.findall(r'^def (\S+)',canonical,re.M);assert len(old_names)==185
cuts=[names.index(old_names[k]) if k<185 else len(names) for k in cuts]
check='--check'in sys.argv;rows=[];prev='PV_B3P_Discriminant227'
for i,(a,b)in enumerate(zip(cuts,cuts[1:])):
 module=f'PV_B3P_E227_{i:02}'
 code=header.replace('import PV_B3P_CompleteTypes227','import '+prev)+''.join(decls[a:b])+'\nend PV_B3P_227\n\n'+''.join('#print axioms PV_B3P_227.'+n+'\n'for n in names[a:b]);q=D/'lean'/(module+'.lean')
 if check:assert q.read_text()==code,q
 else:q.write_text(code)
 rows.append(dict(module=module,source=str(q),first=a,last_exclusive=b,definitions=names[a:b],sha256=hashlib.sha256(code.encode()).hexdigest(),imports=[prev]))
 prev=module
agg='import '+prev+'\n\n#print axioms PV_B3P_227.reference_terminal.reference227\n';q=D/'lean/PV_B3P_CompleteEmission227.lean'
if check:assert q.read_text()==agg
else:q.write_text(agg)
record=dict(canonical_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body_edits=False,explicit_array_size_proofs='arrayproof227-resume5.json',constant_let_lifting='constant227-resume5.json',type_annotations='typed227-resume5.json',pure_bind_normalization='pure227-resume5.json',array_type_annotations='arraytypes227-resume5.json',pure_array_sharing='share227-resume5.json',partition='ordered complete declaration blocks; metadata header/options preserved; previous-chunk import only',chunks=rows,monolithic_stop=dict(attempt=42017,reason='controlled SIGTERM after RSS8923448KiB in six-minute review; no cap increase; isolate declarations instead of retrying aggregation'),aggregator_sha256=hashlib.sha256(agg.encode()).hexdigest())
if not check:(D/'split227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(chunks=len(rows),definitions=len(names),checked=check)))
