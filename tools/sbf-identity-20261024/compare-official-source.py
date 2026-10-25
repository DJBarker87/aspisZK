#!/usr/bin/env python3
"""Fetch exact declared official commit metadata, trees and small source blobs."""
import urllib.request,json,hashlib,time,resource,subprocess
from pathlib import Path
E=Path('evidence/sbf-identity-20261024');t=time.monotonic();rows=[]
commit='790f1537507dbdb0da320fbb3b1c1eca3b33c474';base='https://api.github.com/repos/anza-xyz/rust'
def fetch(url,name):
 a=time.monotonic();req=urllib.request.Request(url,headers={'User-Agent':'Aspis-SBF-identity-metadata'})
 with urllib.request.urlopen(req,timeout=30) as r:
  b=r.read(5000001);status=r.status
 assert len(b)<=5000000,'metadata exceeds bound'
 (E/name).write_bytes(b);rows.append(dict(url=url,http_status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),wall_seconds=time.monotonic()-a,exit=0))
 return b
c=json.loads(fetch(base+'/commits/'+commit,'rust-commit.json'))
top=json.loads(fetch(base+'/git/trees/'+c['commit']['tree']['sha'],'rust-top-tree.json'))
library=next(x for x in top['tree'] if x['path']=='library')
lib=json.loads(fetch(base+'/git/trees/'+library['sha']+'?recursive=1','rust-library-tree.json'));assert not lib['truncated']
x=json.load(open(E/'current-content.json'));selected=x['selected_source'];comparisons=[]
for path,pin in selected.items():
 b=fetch('https://raw.githubusercontent.com/anza-xyz/rust/'+commit+'/'+path,'official-'+path.replace('/','_')+'.txt')
 comparisons.append(dict(path=path,current_sha256=pin['sha256'],official_sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),match=hashlib.sha256(b).hexdigest()==pin['sha256']))
fetch('https://raw.githubusercontent.com/anza-xyz/rust/'+commit+'/.gitmodules','rust-gitmodules.txt')
src=next(x for x in top['tree'] if x['path']=='src');st=json.loads(fetch(base+'/git/trees/'+src['sha'],'rust-src-tree.json'))
u=resource.getrusage(resource.RUSAGE_SELF)
(E/'official-source-comparison.json').write_text(json.dumps(dict(declared_commit=commit,comparisons=comparisons,llvm_submodule=[x for x in st['tree'] if x['path']=='llvm-project'],scope='Current installed selected full files vs exact declared official commit. No historical compiler/source join established.',receipt=dict(command=['python3','tools/sbf-identity-20261024/compare-official-source.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),exit=0,results=rows,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: metadata only')),indent=2)+'\n')
print(json.dumps(comparisons,indent=2))
