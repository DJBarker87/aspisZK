"""Read-only evidence/source/resource/standard-axiom checks; no compiler launches."""
from pathlib import Path
import json,hashlib,re,subprocess,base64
E=Path(__file__).resolve().parent;R=E.parents[1]
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];accepted={}
for n in range(1,101):
    a=f'RPx_{n:03}';d=E/a;r=load(d/'receipt.json');assert r['attempt']==a
    assert r['kind']=='lean' and len(r['sources'])==1
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert str(r['swaps'])=='0'
    assert '-M7000' in r['command'] and '-j1' in r['command'] and '-DElab.async=false' in r['command']
    for source,h in r['source_hashes'].items():assert sha(d/'sources'/source)==h,(a,source)
    assert (E/(a+'-barrier.log')).is_file() and (E/(a+'-reservation.json')).is_file()
    if r['exit_status']==0:
        for line in r['print_axioms']:
            assert 'sorryAx' not in line and not re.search(r'(?<!\w)(?:Lean\.ofReduceBool|native_decide)(?!\w)',line)
            if 'depends on axioms:' in line:
                axioms=line.split('depends on axioms:',1)[1].strip().strip('[]').split(', ')
                assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(a,line)
        for source,h in r['source_hashes'].items():
            if sha(R/'lean'/source)==h:accepted[source]=dict(attempt=a,source_sha256=h,axioms=r['print_axioms'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],revision=r['source_revision'])
    receipts.append(r)
modules=sorted((R/'lean').glob('RPx_*.lean'))
for p in modules:
    assert p.name in accepted,('no exact-source successful receipt',p.name)
    s=p.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|(?m:^\s*axiom\s)|(?:maxHeartbeats|maxRecDepth)',s),p
    names=re.findall(r'(?m)^(?:private )?theorem\s+(\w+)',s)
    audits=re.findall(r'(?m)^#print axioms (\S+)',s)
    assert set(names)<={x.split('.')[-1] for x in audits},(p,names,audits)
    for name in names:
        assert any('.'+name+"'" in a for a in accepted[p.name]['axioms']),(p,name)
changes=subprocess.check_output(['git','diff','--name-only','8c68f136b3cfe0f4d2d83e8f199ea1f8bfc53356'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/RPx_') or p.startswith('evidence/rejected-prefix-20261026/') for p in changes),changes
assert not any(p.endswith(('.olean','.olean.private','.olean.server','.tar','.gz','.so','.elf')) for p in changes)
source=load(E/'RPx_source_check.json');assert not source['substantive_mismatches']
premises=load(E/'RPx_premises.json');assert not premises['removed_rows'] and not premises['added_rows']
for key,item in load(E/'RPx_raw_log_bytes.json').items():
    raw=base64.b64decode(item['original_base64'])
    assert hashlib.sha256(raw).hexdigest()==item['original_sha256']
    assert sha(E/key)==item['display_sha256']
    if key.endswith('/stdout.log'):assert load(E/key.split('/')[0]/'receipt.json')['exit_status']!=0
summary=dict(lean_attempts=len(receipts),kani_runs=0,successes=sum(r['exit_status']==0 for r in receipts),failures=[r['attempt'] for r in receipts if r['exit_status']!=0],current_modules=len(modules),current_module_receipts=accepted,measured_wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,top=accepted['RPx_Top.lean'],nonvacuity=accepted['RPx_Nonvacuity.lean'],standard_axioms_only=True,source_scope_ok=True,package_replay=False,dependency_builds=0,shipped_changes=False,elf_rebuild_trigger=False,physical_source_omission_found=False,L181_removed=False)
(E/'RPx_FINAL.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'RPx_attempts.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in receipts))
print(json.dumps({k:v for k,v in summary.items() if k not in {'current_module_receipts','top','nonvacuity'}}))
