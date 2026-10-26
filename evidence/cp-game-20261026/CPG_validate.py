"""Read-only final CPG source, receipt, and scope validation; no proof launcher."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('CPG_L*/receipt.json'))]
assert len(receipts)<=100
assert len({r['attempt'] for r in receipts})==len(receipts)
final={}
for p in sorted((ROOT/'lean').glob('CPG_*.lean')):
    code=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',code,re.M),p
    matches=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
    assert matches,p
    r=matches[-1]
    final[p.name]={'sha256':sha(p),'attempt':r['attempt'],'axioms':r['print_axioms']}
for r in receipts:
    assert r['command'][4]=='-M7000'
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert int(r['swaps'])==0
    assert r['source_revision'] and r['source_hashes'] and r['deps_fingerprint']['selected_objects']
    if r['exit_status']==0:
        for line in r['print_axioms']:
            if 'depends on axioms:' in line:
                names=line.split('[',1)[1].rstrip(']').split(', ')
                assert set(names)<={'propext','Classical.choice','Quot.sound'},line
last=json.loads((E/'CPG_L041/receipt.json').read_text())
assert last['exit_status']==0 and len(last['print_axioms'])==24
assert last['source_hashes']['CPG_Statements.lean']==final['CPG_Statements.lean']['sha256']
changed=subprocess.check_output(['git','diff','--name-only','b6bc3d3965','HEAD'],cwd=ROOT,text=True).splitlines()
assert all(x.startswith('lean/CPG_') or x.startswith('evidence/cp-game-20261026/') for x in changed)
result={'lean_attempts':len(receipts),'kani_runs':0,'pass':sum(r['exit_status']==0 for r in receipts),'failed':sum(r['exit_status']!=0 for r in receipts),'wall_seconds':sum(r['wall_seconds'] for r in receipts),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'swaps':0,'final_audit':last['attempt'],'axiom_audits':len(last['print_axioms']),'sources':final,'shipped_changes':False,'elf_rebuild_trigger':False,'whole_budget_exhausted':False}
(E/'CPG_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'CPG_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in receipts))
log=(E/'CPG_L041/stdout.log').read_text()
for name,start,end in [('CPG_BEFORE_Top.lean.txt','@AspisR1.T2R_Top.deployed :','@AspisR1.CPG_Top.deployed :'),('CPG_AFTER_Top.lean.txt','@AspisR1.CPG_Top.deployed :','@AspisR1.CPG_Pair.accepted :')]:
    (E/name).write_text(log[log.index(start):log.index(end)])
print(json.dumps({k:v for k,v in result.items() if k!='sources'},indent=2))
