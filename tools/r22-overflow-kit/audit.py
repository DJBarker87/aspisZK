#!/usr/bin/env python3
"""Read-only proof-packet audit; no Lean/Kani/regression rerun."""
import collections,csv,hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'docs/research/100bit-spend-path-20261013/evidence/r22-overflow-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)

def audit():
    snapshots=json.loads((OUT/'source-snapshot-index.json').read_text());index={r['attempt']:r for r in snapshots}
    kani=[]
    for p in sorted((OUT/'kani').glob('*/receipt.json')):
        r=json.loads(p.read_text());s=OUT/index[r['attempt']]['source_snapshot']
        assert sha((s/'source-pins.json').read_bytes())==r['deps_fingerprint']
        for n,h in r['inputs'].items():assert sha((s/n).read_bytes())==h,(p,n)
        assert sha(json.dumps(r['inputs'],sort_keys=True).encode())==r['source_sha256']
        for key in ['module','attempt','source_revision','source_sha256','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:assert key in r,(p,key)
        assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
        cmd=r['command'];assert not any(t in cmd for t in ['--no-overflow-checks','--no-memory-safety-checks','--no-default-checks','--no-undefined-function-checks','--no-unwinding-checks'])
        if (p.parent/'stdout.log').exists():assert sha((p.parent/'stdout.log').read_bytes())==r['stdout_sha256']
        if r['verification_success']:
            assert r['exit_status']==0 and r['checks_by_result'].get('FAILURE',0)==0,p
        kani.append(r)
    lean=[];names=set()
    for p in sorted((OUT/'receipts').glob('*/command.json')):
        r=json.loads(p.read_text());assert r['exit']==0,p
        for key in ['module','source_sha256','deps_fingerprint','exit','wall_s','peak_rss_bytes','process_swaps','source_revision','axioms']:assert key in r,(p,key)
        reports=r['axioms'];assert reports,p
        for line in reports:
            m=re.match(r"'([^']+)'",line);assert m,line;names.add(m[1])
            ax=re.search(r'\[([^\]]*)\]',line)
            if ax:assert {x.strip() for x in ax[1].split(',')}<= {'propext','Classical.choice','Quot.sound'},line
            else:assert 'does not depend on any axioms' in line,line
        src=ROOT/r['source']
        if src.name=='R22OverflowWorkerControl.lean' and sha(src.read_bytes())!=r['source_sha256']:
            # Superseded successful attempt differs only by replacing decide
            # on the concrete counterexample with symbolic omega.
            original=src.read_text().replace('¬ (18446744073709551615 + 1 < 18446744073709551616) := by omega','¬ (18446744073709551615 + 1 < 18446744073709551616) := by decide')
            assert sha(original.encode())==r['source_sha256']
        else:assert sha(src.read_bytes())==r['source_sha256']
        lean.append(r)
    assert len(names)==9,names
    base='b89c4bae8'
    endpoint='docs/research/100bit-spend-path-20261013/lean/R1FinalSoundnessHeadline.lean'
    assert git('show',base+':'+endpoint)==(ROOT/endpoint).read_bytes()
    changed=git('diff','--name-status',base,'--','crates','programs').decode().strip();assert not changed,changed
    forbidden=git('diff','--name-only',base,'--','docs/research/100bit-spend-path-20261013/lean-candidates').decode().strip();assert not forbidden,forbidden
    table=list(csv.DictReader((OUT/'operation-results.tsv').open(),delimiter='\t'))
    census=json.loads((OUT/'operation-census.json').read_text())
    assert {r['site'] for r in table}=={r['id'] for r in census['operations']}
    assert len(table)==len(census['operations'])
    assert len({r['id'] for r in census['operations']})==len(census['operations'])
    assert len({r['site'] for r in table})==len(table)
    result=dict(schema='r22-final-read-only-audit-v1',source_revision=git('rev-parse','HEAD').decode().strip(),kani_attempts=len(kani),kani_successes=sum(r['verification_success'] for r in kani),kani_rejected_or_stopped=[r['attempt'] for r in kani if not r['verification_success']],kani_wall_seconds=sum(r['wall_seconds'] for r in kani),kani_peak_rss_kib=max(r['peak_rss_kib'] for r in kani),kani_total_swaps=sum(r['swaps'] for r in kani),lean_attempts=len(lean),unique_new_theorems=sorted(names),lean_peak_rss_bytes=max(r['peak_rss_bytes'] for r in lean),lean_total_swaps=sum(r['process_swaps'] for r in lean),lean_axioms='standard only',endpoint_sha256=sha((ROOT/endpoint).read_bytes()),endpoint_signature_change='none; h_R22 retained',shipped_source_changes=False,protected_candidate_changes=False,source_snapshots_verified=len(snapshots),inventory_sites=len(table),r22_status='OPEN: conditional local arithmetic and body steps; no frozen two-cone accepted-run composition')
    (OUT/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':audit()
