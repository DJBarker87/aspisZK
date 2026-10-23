#!/usr/bin/env python3
"""Compare every retained adapter helper before the replaced caller stages."""
import hashlib,json,re,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023'
x=json.loads((E/'source-inputs.json').read_text());path='programs/r1-cost-probe/src/r1_pool_adapter.rs'
a=subprocess.check_output(['git','show',x['comparison_source_revision']+':'+path],cwd=R).decode();b=(R/path).read_text()
old_prefix=a[:a.index('#[path = "r1_pool_adapter_owned.rs"]')]
new_prefix=b[:b.index('#[path = "r1_pool_adapter_owned.rs"]')]
assert old_prefix==new_prefix
rows=[]
for m in re.finditer(r'^fn (\w+)',old_prefix,re.M):
 start=m.start();body=old_prefix.index('{',m.end());depth=0;end=None
 # These retained helpers contain no braces in string literals or comments;
 # remove literal/comment tokens while preserving positions before counting.
 clean=re.sub(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*[\s\S]*?\*/',lambda z:' '*len(z[0]),old_prefix)
 for i in range(body,len(clean)):
  if clean[i]=='{':depth+=1
  elif clean[i]=='}':
   depth-=1
   if depth==0:end=i+1;break
 assert end is not None and a[start:end]==b[start:end]
 cut=a[start:end].encode();rows.append(dict(name=m[1],start_line=a.count('\n',0,start)+1,end_line=a.count('\n',0,end)+1,bytes=len(cut),sha256=hashlib.sha256(cut).hexdigest(),status='BYTE_IDENTICAL'))
assert len(rows)==27,len(rows)
x=dict(old_revision=x['comparison_source_revision'],new_revision=x['source_revision'],path=path,unchanged_prefix_bytes=len(old_prefix.encode()),prefix_sha256=hashlib.sha256(old_prefix.encode()).hexdigest(),helpers=rows,scope='All 27 top-level helper bodies before caller stages, exact source text. H5 child changes are listed in source-delta.json; no child-wide identity is claimed. No transitive execution refinement inferred.')
(E/'child-pins.json').write_text(json.dumps(x,indent=2)+'\n');print(len(rows))
