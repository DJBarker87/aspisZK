#!/usr/bin/env python3
"""Pin declaration spans against the inherited S2 source snapshot; no builds."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'evidence/child-joins-20261023'
manifest=json.loads((E/'source-pins.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
def spans(data):
    s=data.decode(); found={}; counts={}
    # Braces in comments and quoted strings must not change the brace depth.
    masked=re.sub(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"',lambda m:' '*len(m[0]),s)
    for m in re.finditer(r'\bfn\s+(\w+)\s*(?:<|\()',masked):
        name=m[1]; counts[name]=counts.get(name,0)+1;key=name+'#'+str(counts[name])
        start=masked.find('{',m.end()); end=start+1; depth=1
        if start<0:continue
        while depth and end<len(masked):
            depth+=(masked[end]=='{')-(masked[end]=='}');end+=1
        assert depth==0,key
        body=s[m.start():end].encode()
        found[key]=dict(sha256=sha(body),start_line=s.count('\n',0,m.start())+1,end_line=s.count('\n',0,end)+1)
    return found
rows=[]
for item in manifest['files']:
    p=item['path'];old=subprocess.check_output(['git','show',manifest['comparison_revision']+':'+p],cwd=R);new=(R/p).read_bytes()
    a,b=spans(old),spans(new)
    for key in sorted(a.keys()|b.keys()):
        rows.append(dict(path=p,declaration=key,historical=a.get(key),current=b.get(key),changed=a.get(key,{}).get('sha256')!=b.get(key,{}).get('sha256')))
x=dict(comparison_revision=manifest['comparison_revision'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),declarations=rows,qualification='Exact lexical function spans; occurrence ordinals distinguish impl methods. No transitive dependency, extracted-body equality or release artifact claim.')
(E/'function-pins.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(function_spans=len(rows),changed=[r['path']+':'+r['declaration'] for r in rows if r['changed']])))
