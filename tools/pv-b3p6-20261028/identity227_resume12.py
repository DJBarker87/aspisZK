"""b3p6-1 audit of every lexical-identity candidate, fail closed.
Inputs are rustc post-expansion text and a fresh exact-output extraction receipt.
An absent extracted body is not inferred from an identical source wrapper.
"""
from pathlib import Path
import re, json, hashlib, difflib
D=Path('evidence/pv-b3p6-20261028'); O=D/'resume12'
sha=lambda b: hashlib.sha256(b).hexdigest()
lex=re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|r(\#*)"[\s\S]*?"\1|"(?:\\.|[^"\\])*"|\w+|[^\s]')
def tokens(s):
    return [(m[0],m.start(),m.end()) for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def close(ts,i):
    depth=1;j=i+1
    while depth:
        depth+=(ts[j][0]=='{')-(ts[j][0]=='}');j+=1
    return j
def module(s,name):
    ts=tokens(s)
    matches=[i+2 for i in range(len(ts)-2) if [t[0] for t in ts[i:i+3]]==['mod',name,'{']]
    assert len(matches)==1,(name,matches)
    i=matches[0];j=close(ts,i)
    return s[ts[i][2]:ts[j-1][1]]
def functions(s):
    ts=tokens(s);out=[]
    for i in range(len(ts)-2):
        if ts[i][0]!='fn':continue
        name=ts[i+1][0];j=i+2
        depth=0
        while j<len(ts):
            v=ts[j][0]
            if depth==0 and v in ['{',';']:break
            if v in ['(','[']:depth+=1
            if v in [')',']']:depth-=1
            j+=1
        if j==len(ts) or ts[j][0]==';':continue
        k=close(ts,j)
        out.append(dict(name=name,tokens=[t[0] for t in ts[i:k]],text=s[ts[i][1]:ts[k-1][2]]))
    return out
inputs=json.loads((O/'charon-inputs.json').read_text())['inputs']
for path,digest in inputs.items():
    local=Path(path)
    if local.is_file():assert sha(local.read_bytes())==digest,path
inv=json.loads((D/'resume9/body-inventory.json').read_text())
reach=json.loads((D/'resume11/reachability.json').read_text())
expanded={n:(O/('expanded-'+n+'.rs')).read_text() for n in ['owned','statement','deployed']}
mods={'terminal':('host_terminal','reference_terminal'),'copy':('host_copy_terminal','reference_copy_terminal'),'field':('host_terminal_field','reference_field'),'poseidon':('state_only_poseidon','reference_poseidon')}
tables={}
for fam,(src,owned) in mods.items():
    tables[fam,'source']=functions(module(expanded['statement' if fam=='poseidon' else 'deployed'],src))
    tables[fam,'owned']=functions(module(expanded['owned'],owned))
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
blocks=re.split(r'(?=^/-- \[)',raw,flags=re.M)
reproduction=json.loads((O/'aeneas-outputs.json').read_text())
reproduced=next(r for r in reproduction if r['path'].endswith('/Funs.lean'))
exact_output=reproduced['byte_identical'] and reproduced['sha256']==sha(raw.encode())
rows=[]
for r in reach['bodies']:
    if r['classification']!='reachable-conservative' or r['status']!='identical':continue
    b=inv['bodies'][r['inventory_index']];row={k:r[k] for k in ['inventory_index','family','key']}
    selected={};errors=[]
    for side in ['source','owned']:
        choices=[v for v in tables[r['family'],side] if v['name']==b[side]['name']]
        scores=[(difflib.SequenceMatcher(None,b[side]['tokens'],v['tokens'],autojunk=False).ratio(),v) for v in choices]
        scores.sort(key=lambda x:x[0],reverse=True)
        if not scores or (len(scores)>1 and scores[0][0]==scores[1][0]):
            errors.append(side+' missing or ambiguous expanded body');continue
        selected[side]=scores[0][1]
        row[side]=dict(expanded_body_sha256=sha(selected[side]['text'].encode()),token_sha256=sha('\0'.join(selected[side]['tokens']).encode()),token_count=len(selected[side]['tokens']),selection_similarity=scores[0][0])
    identity=len(selected)==2 and selected['source']['tokens']==selected['owned']['tokens']
    if not identity:errors.append('post-macro token identity failed')
    f='reference_'+('copy_terminal' if r['family']=='copy' else r['family'])+'.rs'
    emitted=[]
    for block in blocks:
        if f"Source: '{f}', lines {b['owned']['line']}:" in block:
            m=re.search(r'^def (\S+)',block,re.M)
            if m:emitted.append(dict(name='PV_B3P_227.'+m[1],raw_block_sha256=sha(block.encode())))
    if not emitted:errors.append('no extracted declaration at exact owned source span')
    if not exact_output:errors.append('fresh pinned extraction not byte-identical')
    row.update(post_macro_identity=identity,exact_extraction=bool(emitted) and exact_output,model_declarations=emitted,bound=not errors,failures=errors,evidence_class='reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)' if not errors else 'UNBOUND',extraction_record='aeneas-outputs.json',model_scope='immutable raw extracted model; compiled API ports and dependency closure remain separately audited')
    rows.append(row)
out=dict(ruling='b3p6-1 / D455',inventory_sha256=sha((D/'resume9/body-inventory.json').read_bytes()),expanded_hashes={n:sha(s.encode()) for n,s in expanded.items()},fresh_exact_output=exact_output,reachable_candidates=79,lexical_candidates=len(rows),reclassification_bound=sum(r['bound'] for r in rows),own_1_proved=0,bodies=rows,reachability='conservative 79-candidate source cone; exact deployed reachability not certified')
(O/'identity-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['bodies','expanded_hashes']}))
print(json.dumps([dict(index=r['inventory_index'],key=r['key'],failures=r['failures']) for r in rows if not r['bound']]))
