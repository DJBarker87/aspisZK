"""Read-only source/receipt validation; no compiler, launcher or build logic."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text())
start = load(E/'NP6_start.json')
for name, pin in start['pins'].items():
    assert sha(ROOT/name) == pin['sha256'], name

def function(path):
    s = path.read_text()
    a = s.index('fn claims(')
    b = s.index('\n}', a)+2
    return s[a:b]
assert function(ROOT/'crates/aspis-r1-cost-probe/src/r1_semantic.rs') == function(E/'NP6_claims/src/NP6_shipped.rs')
assert function(E/'NP6_reference_origin.rs') == function(E/'NP6_claims/src/NP6_reference.rs')
assert sha(E/'NP6_reference_origin.rs') == load(E/'NP6_binding.json')['reference_sha256']
wire = (ROOT/'crates/aspis-r1-cost-probe/src/r1_wire.rs').read_bytes()
assert (E/'NP6_claims/src/NP6_wire.rs').read_bytes().startswith(wire)
assert sha(ROOT/'crates/aspis-r1-cost-probe/src/sampler.rs') == sha(E/'NP6_claims/src/NP6_sampler.rs')
core = load(E/'NP6_core-validation.json')
assert core['exit'] == 0
for name, digest in core['pins'].items():
    assert sha(ROOT/'crates/aspis-core'/name) == digest, name

receipts = {p.parent.name: load(p) for p in E.glob('NP6_*/receipt.json')}
assert all(f'NP6_L{i:03}' in receipts for i in range(1,30))
assert all(f'NP6_K{i:03}' in receipts for i in range(1,31))
limits = {'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for name,r in receipts.items():
    assert r['limits'] == limits, name
    for source,digest in r['source_hashes'].items():
        snap = E/name/'sources'/source
        assert sha(snap) == digest, (name,source)
    if name.startswith('NP6_K'):
        assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL'] == '3', name

accepted = [6,11,13,14,15,*range(17,26),29,30]
for i in accepted:
    name=f'NP6_K{i:03}'; r=receipts[name]
    assert r['exit_status']==0, name
    command=' '.join(r['command'])
    assert '--stub' not in command and '--no-memory-safety-checks' not in command
    selected=r['command'][r['command'].index('--harness')+1].split('::')[0]
    stable=['NP6_claims/Cargo.toml','NP6_claims/src/NP6_shipped.rs','NP6_claims/src/NP6_reference.rs','NP6_claims/src/NP6_sampler.rs',f'NP6_claims/src/{selected}.rs']
    for source in stable:
        assert sha(E/source)==r['source_hashes'][source], (name,source)
    assert (E/name/'sources/NP6_claims/src/NP6_wire.rs').read_bytes().startswith(wire),name
    for source in (E/name/'sources').rglob('*.rs'):
        assert not re.search(r'kani::(?:assume|stub)\s*[(!]',source.read_text()), source
    assert 'VERIFICATION:- SUCCESSFUL' in (E/name/'stdout.log').read_text(),name
for i in [29,30]:
    cmd=receipts[f'NP6_K{i:03}']['command']
    assert '--memory-leak-check' in cmd and '--memory-cleanup-check' in cmd

lean=[]
for p in sorted((ROOT/'lean').glob('NP6_*.lean')):
    assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b|\b(?:native_decide|sorryAx)\b',p.read_text()),p
    matches=[name for name,r in receipts.items() if name.startswith('NP6_L') and r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
    assert matches, p
    lean.append({'source':str(p.relative_to(ROOT)),'sha256':sha(p),'successful_attempts':matches})
    for name in matches:
        for line in receipts[name]['print_axioms']:
            if 'depends on axioms:' in line:
                axioms=line.rsplit('[',1)[1].split(']')[0].replace(',',' ').split()
                assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},(name,line)
assert receipts['NP6_R002']['exit_status']==0
out={'validation':'passed','source_baseline':start['revision'],'lean_attempts':29,'kani_runs':30,
     'accepted_kani':[f'NP6_K{i:03}' for i in accepted], 'lean_sources':lean,
     'note':'K026 allocator diagnostic is not failed-allocation evidence; K027/K028 are excluded profile diagnostics. This check validates bindings, not proof replay.'}
(E/'NP6_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'validation':'passed','lean_sources':len(lean),'accepted_kani':len(accepted),'receipt_count':len(receipts)}))
