"""Validate evidence only. Does not launch or retry a compiler."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];attempts=[]
for rp in sorted(E.glob('KSB_L*/receipt.json')):
    r=json.loads(rp.read_text());attempts.append(r)
    admission=json.loads((E/(r['attempt']+'-admission.json')).read_text())
    if admission['exit_status']!=0 or admission['allowed'] is not True:errors.append('admission '+r['attempt'])
    if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('limits '+r['attempt'])
    if '-M7000' not in r['command']:errors.append('Lean memory limit '+r['attempt'])
    for src,h in r['source_hashes'].items():
        if sha(E/r['attempt']/'sources'/src)!=h:errors.append('snapshot '+src)
        if sha(E/Path(src).name)!=h:errors.append('current source '+src)
    if r['exit_status']!=(1 if r['attempt']=='KSB_L004' else 0):errors.append('unexpected compiler exit '+r['attempt'])
    if r['exit_status']==0:
        for line in r['print_axioms']:
            names=re.search(r'\[(.*)\]',line)
            if names and not set(names[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'}:errors.append('axioms '+line)
for a in ['KSB_L005','KSB_L006','KSB_L007']:
    g={}
    for l in (E/a/'stdout.log').read_text().splitlines():
        if l.startswith('KSB_DEP '):
            r=json.loads(l[8:]);g[r['name']]=r
    for l in (E/'KSB_theorem_receipts.jsonl').read_text().splitlines():
        r=json.loads(l)
        if r.get('attempt')!=a:continue
        path=r['kernel_path']
        if path[0]!=r['name']:errors.append('path root '+r['name'])
        for x,y in zip(path,path[1:]):
            if y not in g.get(x,{}).get('refs',[]):errors.append('invalid edge '+x+' -> '+y)
p=json.loads((E/'KSB_provenance.json').read_text())
for k in ['object_mismatches','objects_without_retained_manifest','sources_without_matching_accepted_receipt','source_mismatches']:
    if p[k]:errors.append(k)
identity=json.loads((E/'KSB_identity.json').read_text())
if len(identity['declaration_bytes'])!=307 or len(identity['restored_edited_declarations'])!=15:errors.append('raw identity coverage')
for r in identity['files']:
    if sha(E/(r['module']+'.lean'))!=r['sha256']:errors.append('identity hash '+r['module'])
result=dict(errors=errors,lean_attempts=len(attempts),lean_pass=sum(r['exit_status']==0 for r in attempts),
    lean_rejected=sum(r['exit_status']!=0 for r in attempts),kani_runs=0,rust_runs=0,
    wall_seconds=sum(r['wall_seconds'] for r in attempts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in attempts),
    swaps=sum(int(r['swaps']) for r in attempts),
    task_status='INCOMPLETE: raw KIT2 lacks shipped dependencies; full three-way recheck blocked',
    no_release_credit=True)
(E/'KSB_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'KSB_attempts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in attempts))
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
