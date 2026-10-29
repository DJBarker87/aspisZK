"""Verify recovered D432 receipts without launching or repeating any compile."""
from pathlib import Path
import hashlib,json,re,subprocess

D=Path('evidence/pv-b3p6-20261028/resume9')
L=D.parent/'lean'
index=json.loads((D/'receipt-index.json').read_text())
t=json.loads((D/'TALLY-resume9.json').read_text())
manifest=json.loads((D/'focused-manifest.json').read_text())
assert len(index)==t['lean_attempts']==100
assert sorted(r['attempt'] for r in index)==sorted(t['used_ids'])==list(range(63100,63200))
assert t['audit_ids_used']==[63197,63198,63199]
admission=json.loads((D/'admission-audit.json').read_text())
assert admission['errors']==[] and admission['void_attempts']==[]
assert len(admission['refusals'])==len(t['refusals'])==0
allowed={'propext','Classical.choice','Quot.sound'}
pattern=r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
latest={};audits=[]
for row in index:
    p=D/row['receipt'];r=json.loads(p.read_text())
    assert r['exit_status']==row['exit'] and r['swaps']==0
    assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
    assert r['command'][-1]=='7000'
    for gate in ['reservation.json','barrier.json']:
        assert json.loads((p.parent.parent/gate).read_text())['allowed'] is True
    raw=(p.parent.parent/'source.lean').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==r['source_sha256']==row['source_sha256']
    assert subprocess.check_output(['git','show',r['lean_source_revision']+':'+str(L/(r['module']+'.lean'))])==raw
    log=(p.parent/'stdout.log').read_text()+'\n'+(p.parent/'stderr.log').read_text()
    if row['exit']==0:
        assert 'sorryAx' not in log
        for m in re.finditer(pattern,log,re.M):
            assert {a.strip() for a in (m[2] or '').split(',') if a.strip()}<=allowed
        latest[row['module']]=row
    if row['attempt']>=63197:
        assert row['exit']==0
        audits.append(row)
for module,row in latest.items():
    assert hashlib.sha256((L/(module+'.lean')).read_bytes()).hexdigest()==row['source_sha256']
axioms=next(r for r in index if r['attempt']==63198)
log=(D/axioms['receipt']).parent.joinpath('stdout.log').read_text()
actual=[m[1] for m in re.finditer(pattern,log,re.M)]
assert sorted(actual)==sorted(manifest['new_theorems']) and len(set(actual))==len(actual)
for row in manifest['sources']:
    assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
external=json.loads((D/'external-verification-resume9.json').read_text())
cache=json.loads((D/'cache-verification-resume9.json').read_text())
assert external['checked_before_any_compile'] and external['mismatches']==[] and cache['mismatches']==[]
assert not [p for p in D.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
summary=dict(charged_attempts=100,passed=sum(r['exit']==0 for r in index),rejected=sum(r['exit']!=0 for r in index),
    audit_ids=t['audit_ids_used'],audited_theorems=len(actual),accepted_axioms=sorted(allowed),
    source_snapshots_verified=100,source_revision_blobs_verified=100,current_accepted_modules=len(latest),
    external_objects_verified_before_first_compile=external['checked_count'],retained_objects_verified=cache['checked_count'],
    max_process_rss=max(index,key=lambda r:r['peak_rss_kib']),all_swap_zero=True,
    refusals_uncharged=0,void_attempts=[],native_scopes=0,kani_runs=0,
    audit_source_revision=audits[0]['lean_source_revision'],target_established=False,runjoin_op227_discharged=False,
    full_endpoint_manifest_replayed=False,recovery='audits already completed before capacity relaunch; recovered read-only; no rerun',
    semantic_use='reclassification within existing Charon/Aeneas tool trust')
(D/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
