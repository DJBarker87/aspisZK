"""Conservative per-theorem receipts; kernel paths, never import-use guesses."""
from pathlib import Path
import collections, hashlib, json, re

E=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
    out=list(s);i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-':out[i:i+2]='  ';depth+=1;i+=2
            elif s[i:i+2]=='-/':out[i:i+2]='  ';depth-=1;i+=2
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif s[i:i+2]=='/-' and not string:out[i:i+2]='  ';depth=1;i+=2
        elif s[i:i+2]=='--' and not string:
            j=s.find('\n',i);j=len(s) if j<0 else j;out[i:j]=' '*(j-i);i=j
        else:
            if s[i]=='"' and (i==0 or s[i-1]!='\\'):string=not string
            i+=1
    return ''.join(out)
def declarations(p):
    s=p.read_text();c=clean(s)
    ms=list(re.finditer(r'(?m)^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(def|abbrev|structure|inductive|theorem|lemma|opaque)\s+([^\s{(:]+)',c))
    for i,m in enumerate(ms):
        stack=[]
        for line in c[:m.start(1)].splitlines():
            n=re.match(r'^\s*namespace\s+(\S+)',line)
            if n:stack.append(n[1]);continue
            if re.match(r'^\s*(noncomputable\s+)?section\b',line):stack.append('');continue
            if re.match(r'^\s*end(?:\s|$)',line) and stack:stack.pop()
        prefix='.'.join(x for x in stack if x)
        end=ms[i+1].start() if i+1<len(ms) else len(s)
        yield dict(name=(prefix+'.' if prefix else '')+m[2],kind=m[1],line=s[:m.start(1)].count('\n')+1,
                   span_sha256=hashlib.sha256(s[m.start():end].encode()).hexdigest())

inventory=json.loads(Path('evidence/kit-audit1-20261027/KSA_inventory.json').read_text())
seeds={}
for r in inventory['rows']:
    if not Path(r['file']).stem.startswith('XRn_Join_'):continue
    if Path(r['file']).stem in ['XRn_Join_Types','XRn_Join_TypesExternal']:continue
    if r['kind'] not in ['def','abbrev']:continue
    name=r['kernel_name']
    if Path(r['file']).stem=='XRn_Join_Funs':
        seeds[name]=dict(reason='edited emitted declaration restored to raw body',file=r['file'],line=r['line'],raw_line=r['raw_body_line'])
    elif r['name'].startswith(('aspis_core.','aspis_statement.','verifier.','compact.','r1_wire.','r1_semantic.','sampler.','transcript.','fast_pairing.')) or r['verdict']=='UNFAITHFUL':
        seeds[name]=dict(reason='removed shipped-function stand-in',file=r['file'],line=r['line'],verdict=r['verdict'],raw_body_line=r.get('raw_body_line'))
(E/'KSB_removed_definitions.json').write_text(json.dumps(seeds,indent=2)+'\n')

envs=[]
for attempt in ['KSB_L005','KSB_L006','KSB_L007']:
    g={};p=E/attempt/'stdout.log'
    receipt=json.loads((E/attempt/'receipt.json').read_text())
    assert receipt['exit_status']==0
    for line in p.read_text().splitlines():
        if line.startswith('KSB_DEP '):
            r=json.loads(line[8:]);g[r['name']]=r
    reverse=collections.defaultdict(list)
    for n,r in g.items():
        for ref in r['refs']:reverse[ref].append(n)
    # One shortest *exact* path is enough to establish NEEDS-REPROOF.
    paths={n:[n] for n in sorted(seeds) if n in g}
    q=collections.deque(paths)
    while q:
        n=q.popleft()
        for parent in reverse[n]:
            if parent not in paths:paths[parent]=[parent]+paths[n];q.append(parent)
    envs.append((attempt,g,paths,digest(p)))

ix=json.loads((E/'KSB_sources.json').read_text())
rows=[]
for module,path in sorted(ix.items()):
    if not module.startswith(('XR','XS')):continue
    p=Path(path)
    for d in declarations(p):
        if d['kind'] not in ['theorem','lemma']:continue
        r=dict(module=module,file=path,source_sha256=digest(p),**d)
        matches=[(a,g,paths,h) for a,g,paths,h in envs if d['name'] in g and g[d['name']]['module']==module]
        affected=[(a,g,paths,h) for a,g,paths,h in matches if d['name'] in paths]
        if affected:
            a,g,paths,h=affected[0];w=paths[d['name']]
            r.update(classification='NEEDS-REPROOF',kernel_path=w,exact_definition=w[-1],definition=seeds[w[-1]],attempt=a,kernel_stdout_sha256=h)
        else:
            r.update(classification=None,status='BLOCKED: no successful KIT2 environment; no transfer or obsolescence inferred',
                     kernel_inspected=bool(matches),attempts=[a for a,_,_,_ in matches],
                     reason='No path to the removed definitions in the inspected prefix graph' if matches else 'No accepted current kernel environment inspected for this source theorem')
        r['transfer_compile_attempt']=None
        rows.append(r)
(E/'KSB_theorem_receipts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
summary=dict(source_theorem_spans=len(rows),needs_reproof=sum(r['classification']=='NEEDS-REPROOF' for r in rows),
    transfers=0,obsolete=0,blocked=sum(r['classification'] is None for r in rows),
    fresh_kernel_environments=[dict(attempt=a,constants=len(g),stdout_sha256=h) for a,g,_,h in envs],
    caveat='Source-span inventory includes diagnostics/WIP; absent kernel constants are not asserted proved. BLOCKED is explicitly outside the requested completed triage. No whole re-check completion claimed.')
(E/'KSB_classification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
roots=['XSf_Closed.prepare','XSe_HybridCanonical.source','XSe_QueryBasis.source','XSe_NewPhaseSource.source','XSe_HybridSaved.source','XSe_ValidatorTransport.source','XSe_RecordTransport.source','XSe_ParseFinish.driver']
selected=[r for r in rows if r['name'] in roots]
# Keep all exact removed-definition paths for the A2 root, not just one BFS witness.
root='XSf_Closed.prepare';a,g,_,h=envs[0]
visited=set();prev={root:None};q=collections.deque([root])
while q:
    n=q.popleft()
    if n in visited:continue
    visited.add(n)
    for ref in g.get(n,{}).get('refs',[]):
        if ref not in prev:prev[ref]=n;q.append(ref)
paths=[]
for n in sorted(seeds.keys() & visited):
    w=[];v=n
    while v is not None:w.append(v);v=prev[v]
    paths.append(dict(definition=n,path=list(reversed(w)),detail=seeds[n]))
(E/'KSB_A2_dependencies.json').write_text(json.dumps(dict(root=root,attempt=a,status='NEEDS-REPROOF',
    removed_definition_paths=paths,reachable_recorded_constants=sorted(visited),
    completeness='Exact paths through XR/XS/LP-owned constants in the selected old environment; not a complete all-owner dependency list against KIT2.',
    statement_source='evidence/extraction-assoc24-20261027/XSf_Closed.lean',
    axioms=['propext','Classical.choice','Quot.sound']),indent=2)+'\n')
(E/'KSB_selected_roots.json').write_text(json.dumps(selected,indent=2)+'\n')
print(json.dumps(summary,indent=2))
for r in selected:print(r['name'],r['classification'],r.get('kernel_path'))
