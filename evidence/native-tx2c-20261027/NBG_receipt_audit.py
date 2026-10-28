"""Audit saved receipts and metadata; does not launch a prover/build."""
from pathlib import Path
import json, hashlib, subprocess, tomllib, re

E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
lock=subprocess.check_output(['git','show',rev+':Cargo.lock'])
locksha=hashlib.sha256(lock).hexdigest()
key=lambda p:(p['name'],p['version'],p.get('source'))
frozen={key(p):p for p in tomllib.loads(lock.decode())['package']}
metadata={}
for line in (E/'NBG_K_TRANSPORT.jsonl').read_text().splitlines():
    x=json.loads(line)
    if '"packages"' not in x.get('stdout',''):continue
    objects=[json.loads(s) for s in x['stdout'].splitlines() if s.startswith('{')]
    for m in objects:
        if 'packages' in m:metadata[x['attempt']]=m
checks=[]
receipts=[]
for p in sorted(E.glob('NBG_*/receipt.json')):
    r=json.loads(p.read_text());a=r['attempt'];receipts.append(r)
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
    assert str(r['swaps'])=='0',a
    for ax in r.get('print_axioms',[]) if r['exit_status']==0 else []:
        if 'depends on axioms:' in ax:
            assert set(ax.split('[',1)[1].rstrip(']').split(', ')) <= {'propext','Classical.choice','Quot.sound'},(a,ax)
    if r['kind']!='kani':continue
    m=metadata[a];pkgs={p['id']:p for p in m['packages']};nodes={n['id']:n for n in m['resolve']['nodes']}
    assert {key(p) for p in pkgs.values()}<=frozen.keys(),a
    errors=[]
    for parent in pkgs.values():
        for dep in nodes[parent['id']]['dependencies']:
            q=pkgs[dep]
            matches=[]
            for label in frozen[key(parent)].get('dependencies',[]):
                bits=label.split(' ')
                if bits[0]!=q['name']:continue
                if len(bits)==1 and sum(k[0]==q['name'] for k in frozen)!=1:continue
                if len(bits)>1 and bits[1]!=q['version']:continue
                if len(bits)>2 and bits[2].strip('()')!=q.get('source'):continue
                matches.append(label)
            if not matches:errors.append([key(parent),key(q)])
    assert not errors,(a,errors)
    for suffix in ['before','after']:
        assert (E/(a+'-lock-'+suffix+'.log')).read_text().strip()==locksha,(a,suffix)
    assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
    cfg=json.loads((E/(a+'-reservation.json')).read_text())
    assert cfg['allowed'] is True,a
    checks.append(dict(attempt=a,resolved_packages=len(pkgs),frozen_packages=len(frozen),
                       omitted_unselected_packages=sorted(set(frozen)-{key(p) for p in pkgs.values()},key=str),
                       new_packages=[],edge_errors=[],lock_before=locksha,lock_after=locksha,
                       metadata_sha256=hashlib.sha256(json.dumps(m,sort_keys=True).encode()).hexdigest()))
lean=[r for r in receipts if r['kind']=='lean'];kani=[r for r in receipts if r['kind']=='kani']
assert len(kani)==30 and len(lean)<=100,(len(kani),len(lean))
final=next(r for r in lean if r['attempt']=='NBG_L096')
assert final['exit_status']==0 and len(final['print_axioms'])==84
fields=['attempt','kind','module','command','sources','source_revision','source_hashes','deps_fingerprint',
        'exit_status','wall_seconds','peak_rss_kib','swaps','cgroup','limits','cgroup_memory_peak_bytes','print_axioms']
out=dict(frozen_revision=rev,lock_sha256=locksha,kani_invocations=len(kani),lean_invocations=len(lean),
         setup_only_identifiers=['NBG_K001','NBG_K002','NBG_L006'],
         kani_passing=sum(r['exit_status']==0 for r in kani),
         lean_passing=sum(r['exit_status']==0 for r in lean),
         successful_unchanged_dependency_builds=[r['attempt'] for r in lean if r['exit_status']==0 and not r['module'].startswith('NBG_')],
         final_axioms=final['print_axioms'],
         max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),
         total_wall_seconds=sum(float(r['wall_seconds']) for r in receipts),
         total_swaps=sum(int(r['swaps']) for r in receipts),
         budget_stop='30 actual Kani invocations exhausted; no further proof launches',
         receipts=[{k:r[k] for k in fields if k in r} for r in receipts])
(E/'NBG_GRAPH_AUDIT.json').write_text(json.dumps(checks,indent=2)+'\n')
(E/'NBG_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['receipts','final_axioms']},indent=2))
