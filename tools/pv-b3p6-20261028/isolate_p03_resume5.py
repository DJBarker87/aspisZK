"""Isolate four failed declarations; supply named cons-shape length proofs.
The constant/data expressions and all runtime operations remain unchanged.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'lean/PV_B3P_P227_03.lean';raw=p.read_text()
# Original failed snapshot remains immutable in its receipt; reconstruction is
# from the fresh port generator, not from the post-isolation aggregator.
if 'def reference_poseidon.external_group227'not in raw:raw=(D/'p03-before-isolation-resume5.lean.txt').read_text()
else:(D/'p03-before-isolation-resume5.lean.txt').write_text(raw)
parts=re.split(r'(?=^/-- \[)',raw,flags=re.M);header=parts[0];blocks=parts[1:];assert len(blocks)==4
prev='PV_B3P_P227_02';rows=[]
for j,block in enumerate(blocks):
 block=block.split('\n#print axioms ')[0];block=re.sub(r'\nend PV_B3P_227\s*$','',block)
 edits=[]
 for m in re.finditer(r'Array\.make\s+(\d+)#usize\s+\[',block):
  n=int(m[1]);depth=1;i=m.end();start=i;xs=[]
  while depth:
   c=block[i]
   if c in '[({':depth+=1
   if c in '])}':depth-=1
   if c==',' and depth==1:xs.append(block[start:i].strip());start=i+1
   i+=1
  xs.append(block[start:i-1].strip());assert len(xs)==n,(n,len(xs))
  suffix=' (by simp only [List.length_cons,List.length_nil]; rfl)';assert block[i:].startswith(suffix)
  proof=' (PV_B3P_Length227.size'+str(n)+' '+ ' '.join('('+x+')'for x in xs)+')'
  edits.append((i,i+len(suffix),proof))
 for a,b,v in sorted(edits,reverse=True):block=block[:a]+v+block[b:]
 name=re.search(r'^def\s+(\S+)',block,re.M)[1];module='PV_B3P_P227_03'+chr(97+j)
 code=header.replace('import PV_B3P_P227_02','import '+prev+'\nimport PV_B3P_Length227')+block+'\nend PV_B3P_227\n\n#print axioms PV_B3P_227.'+name+'\n';q=D/'lean'/(module+'.lean');q.write_text(code);rows.append(dict(module=module,name=name,source=str(q),named_length_proofs=len(edits),sha256=hashlib.sha256(code.encode()).hexdigest()));prev=module
p.write_text('import '+prev+'\n\n#print axioms PV_B3P_227.reference_poseidon.external_local_packed_raw\n')
(D/'isolate-p03-resume5.json').write_text(json.dumps(dict(failed_attempt=42067,raw_failed_sha256=hashlib.sha256(raw.encode()).hexdigest(),runtime_data_edits=False,rows=rows),indent=2)+'\n');print(json.dumps(rows))
