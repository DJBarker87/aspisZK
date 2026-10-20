#!/usr/bin/env python3
"""Pinned source census. Includes unreachable/test sites explicitly as a superset."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'docs/research/100bit-spend-path-20261013/evidence/p5-bumps-20261021'
FREEZE='b2727acd3abf79315d18b754a260f58f4b1c6326'
def blob(p):return subprocess.check_output(['git','show',FREEZE+':'+p],cwd=ROOT).decode()
def sha(b):return hashlib.sha256(b.encode() if isinstance(b,str) else b).hexdigest()
def masked(s):
    # Preserve byte offsets/newlines, mask comments and literals for brace counting.
    pat=r'//[^\n]*|/\*[\s\S]*?\*/|b?"(?:\\.|[^"\\])*"'
    return re.sub(pat,lambda m:re.sub(r'[^\n]',' ',m[0]),s)
def fn(p,name):
    s=blob(p); m=masked(s); matches=list(re.finditer(r'\bfn\s+'+re.escape(name)+r'\b',m));assert len(matches)==1,(p,name,len(matches))
    st=m.rfind('\n',0,matches[0].start())+1;start=m.index('{',matches[0].end());depth=1;i=start+1
    while depth:
        depth+=(m[i]=='{')-(m[i]=='}');i+=1
    return s[st:i],s.count('\n',0,st)+1
if __name__=='__main__':
    paths=subprocess.check_output(['git','ls-tree','-r','--name-only',FREEZE,'programs/aspis-pool','programs/r1-cost-probe','programs/aspis-registry','programs/aspis-verifier','crates/aspis-statement/src/pool_v1'],cwd=ROOT,text=True).splitlines()
    rows=[];sources={}
    for p in paths:
        if not p.endswith('.rs'):continue
        s=blob(p);sources[p]=sha(s);owner=None
        for n,line in enumerate(s.splitlines(),1):
            match=re.search(r'\bfn\s+(\w+)',line)
            if match:owner=match[1]
            if re.search(r'\bbump\b|\bbump_\w+|\w+_bump\b|\bhints?\b|\b\w*SEED\w*\b|create_with_seed|create_program_address|find_program_address',line):
                rows.append(dict(path=p,line=n,lexical_owner=owner,text=line,classification='superset; comments, tests and inactive routes included'))
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'source-census.json').write_text(json.dumps(dict(source_revision=FREEZE,source_files=sources,sites=rows),indent=2)+'\n')
    print(json.dumps(dict(files=len(sources),lexical_sites=len(rows),source_revision=FREEZE)))
