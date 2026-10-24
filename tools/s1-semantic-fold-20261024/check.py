#!/usr/bin/env python3
"""Source-only packet validation; no builds, proofs, or remote operations."""
from pathlib import Path
import hashlib, json, re, subprocess
R = Path(__file__).resolve().parents[2]
B = R/'docs/research/100bit-spend-path-20261013'
E = B/'evidence/s126-current-caller-20261021'
P = E/'s1-semantic-fold-controls-20261024'
T = R/'tools/s1-semantic-fold-20261024'
sha = lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
hashtext = lambda s:hashlib.sha256(s.encode()).hexdigest()
def item(s,n):
    start=s.index('fn '+n+'('); end=s.index('{',start)+1; depth=1
    while depth:
        depth += (s[end]=='{')-(s[end]=='}'); end += 1
    return s[start:end]
pins=json.loads((P/'selected-source-pins.json').read_text())
for rev,h in pins['whole_native_files'].items():
    s=subprocess.check_output(['git','-C',str(R),'show',rev+':'+pins['native_source_path']],text=True)
    assert hashtext(s)==h
    for name,row in pins['items'].items():
        assert hashtext(item(s,name))==row['native_item_sha256']
        assert item(s,name)+'\n'==(P/('native-'+name+'.rs')).read_text()
lib=(T/'lib.rs').read_text()
native,reference=lib.split('mod reference {',1)
for name,row in pins['items'].items():
    assert hashtext(item(native,name))==row['native_item_sha256']
    assert hashtext(item(reference,name))==row['reference_item_sha256']
    assert item(reference,name)+'\n'==(P/('reference-'+name+'.rs')).read_text()
prior=P/'prior-extraction'
for phase in ['charon','aeneas']:
    rec=json.loads((prior/f'runs/{phase}-a/receipt.json').read_text())
    assert rec['exit_status']==0
    assert sha(prior/'input/source-pins.json')==rec['source_pins_sha256']
    assert sha(prior/'run-source-call-extraction.py')==rec['runner_sha256']
    for path,h in rec['outputs'].items():
        if path.endswith('.lean'):assert sha(prior/path)==h
for name in ['Types','Funs']:
    path=f'generated/AspisR1SemanticCallExtraction/{name}.lean'
    assert (prior/path).read_bytes()==(B/f'lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/{name}.lean').read_bytes()
accepted={'boundary_same_complete_calls-v3':442,'value_same_complete_calls-v1':566}
native_receipts=[]
for target,checks in accepted.items():
    d=P/'host/results'/target
    r=json.loads((d/'receipt.json').read_text()); inp=json.loads((d/'input.json').read_text())
    assert r['exit_status']==0 and r['swaps']==0 and r['cgroup_swap_current']==0
    assert all(r['sources_unchanged'].values())
    assert sha(d/'input.json')==r['input_sha256']
    assert '--unwinding-assertions' in r['command']
    assert r['limits']['memory.max']==str(2*2**30) and r['limits']['memory.swap.max']=='0'
    log=(d/'stdout.log').read_text()
    assert f'0 of {checks} failed' in log and '1 successfully verified harnesses, 0 failures' in log
    assert 'VERIFICATION:- SUCCESSFUL' in log
    assert inp['environment']['RUSTFLAGS'].startswith('-C opt-level=3 ')
    own=next(v for k,v in inp['source_pins'].items() if 's1-semantic-fold-controls-v1' in k)
    assert own['src/lib.rs']==sha(T/'lib.rs') and own['src/proofs.rs']==sha(T/'proofs.rs')
    assert own['run-host.py']==sha(T/'run-host.py') and own['admit-host.py']==sha(T/'admit-host.py')
    core=next(v for k,v in inp['source_pins'].items() if k.endswith('/aspis-core/Cargo.toml'))
    for field in ['src/field.rs','src/field/wide_exact.rs']:
        raw=subprocess.check_output(['git','-C',str(R),'show','25866ec331cc7ce27dd9956609c11d32fa8fa58a:crates/aspis-core/'+field])
        assert hashlib.sha256(raw).hexdigest()==core[field]
    admission=json.loads((P/'host'/(target+'-admission.json')).read_text())
    assert admission['admitted']
    assert admission['root']=='/sys/fs/cgroup'
    assert admission['reserved_bytes']+admission['additional_bytes']+admission['uncapped_background_allowance_bytes']<admission['limit_bytes']
    assert admission['uncapped_processes'] and admission['all_cgroups']
    native_receipts.append(r)
targets=json.loads((P/'lean-targets.json').read_text())
for name,attempt in targets['targets'].items():
    d=E/attempt;r=json.loads((d/'receipt.json').read_text())
    assert r['exit_status']==0 and r['swaps']==0
    assert sha(d/'source.lean')==sha(B/'lean-candidates/s126-caller-boundary-20261021'/(name+'.lean'))==r['source_sha256']
    audits=r['print_axioms'];assert audits
    assert all('sorryAx' not in x and all(a in ['propext','Classical.choice','Quot.sound'] for a in re.findall(r'\[(.*?)\]',x,re.S)[0].replace('\n','').replace(' ','').split(',')) for x in audits if 'depends on axioms' in x)
    assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(d/'source.lean').read_text())
for path,h in json.loads((P/'tool-pins.json').read_text())['files'].items():assert sha(R/path)==h
assert not any(p.suffix in ['.olean','.llbc','.so','.o','.a'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',native_control_checks=sum(accepted.values()),native_wall_seconds=sum(r['wall_seconds'] for r in native_receipts),native_peak_rss_bytes=max(r['peak_rss_kib'] for r in native_receipts)*1024,lean=targets['metrics'],qualification='Control gates + concrete extracted installation; native numeric/SDK/abort and global soundness remain open.')))
