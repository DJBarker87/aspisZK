"""Focused packet integrity audit, not Lean/native/security/ELF validation."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
D=Path(__file__).resolve().parent;R=D.parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/factory-state'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
subprocess.run(['python3',str(D/'source.py'),'--check'],check=True)
assert not subprocess.check_output(['git','diff','dc26b384f5','--','crates','programs'],cwd=R)
for n in ['reservation.py','reservation_base.py']:
    assert (D/n).read_bytes()==(D.parent/'factory-source'/n).read_bytes()
f=E/'packet/extraction053';failed=json.loads((f/'receipt.json').read_text())
assert failed['exit_status']==1 and failed['actual_target_invocations']==failed['scope_invocations']==0
assert 'factory-iteration/RELATION.md' in (f/'stderr.log').read_text()
assert not (f/'preflight.json').exists() and not (f/'admission-before.json').exists()
o=E/'packet/extraction054';pre=json.loads((o/'preflight.json').read_text());r=json.loads((o/'receipt.json').read_text())
assert r['exit_status']==0 and r['actual_target_invocations']==r['scope_invocations']==1
assert r['postrun_changed_inputs']==[] and r['sysroot_rlib_count']==189
pins=pre['source_sha256'];go=json.loads((o/'go-hashes.json').read_text())
assert pins==go['source_sha256']
assert pre['dependency_fingerprint']==hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest()
host='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/'
for base,prefix in [(o/'source-inputs',host+'factory-state/'),(o/'original-inputs',host)]:
    for p in base.rglob('*'):
        if p.is_file():assert pins[prefix+str(p.relative_to(base))]==sha(p),p
for name in ['admission-before.json','admission-barrier.json']:
    ad=json.loads((o/name).read_text())
    assert ad['allowed'] and ad['reserve_check']
    assert ad['projected_reserved_bytes']<55*2**30
    assert ad['projected_reserved_bytes']+ad['uncapped_resident_reserve_bytes']+7*2**30<ad['meminfo']['MemTotal']
res=json.loads((o/'resources.json').read_text())
assert res['limits']=={'memory.high':str(1536*2**20),'memory.max':str(2*2**30),'memory.swap.max':'0','pids.max':'64'}
assert res['peak_swap_bytes']==0
em=json.loads((E/'emission-audit.json').read_text())
assert em['input']=={k:r['outputs'][0][k] for k in ['sha256','size']}
shape=json.loads((E/'shape-check.json').read_text())
assert shape['actual_backend_invocations']==0
assert any(d['function_id']==15 and d['drop']['statement_id']==796 for d in shape['unsupported_drops'])
assert not (E/'packet/extraction055').exists() and not (E/'packet/extraction056').exists()
objects=json.loads((E/'runner-logs/outputs.json').read_text())
assert objects['actual_compiler_invocations']==0 and len(objects['files'])>0
for root in [D,E]:
    for p in root.rglob('*'):
        if p.is_file():
            assert p.suffix not in ['.olean','.o','.rlib','.rmeta','.elf','.so','.exe','.llbc','.pyc'],p
            if p.suffix=='.json': assert p.stat().st_size<=5_000_000,p
ledger=dict(schema='ProverRwFactoryState-budget-v1',entry_revision='dc26b384f5',
    extraction=dict(entry_charged=52,ceiling=56,charged_now=54,remaining=2,
        this_step=[dict(slot=53,charged=1,scope_invocations=0,actual_extractions=0,reason='missing input guard failure'),dict(slot=54,charged=1,scope_invocations=1,actual_extractions=1,kind='Charon')],
        actual_charon_this_step=1,actual_aeneas_this_step=0,
        historical_050_051_052='unchanged: three charged pre-extraction denials; no actual extraction'),
    backend=dict(used=15,ceiling=16,new_invocations=0),Lean=dict(used=236,ceiling=260,new_invocations=0),
    Kani=dict(used=57,ceiling=60,new_invocations=0,last_slot_reserved=True),
    optimized_Rust_checks_tests=dict(used=0,ceiling=3),ELF_commands=dict(used=0,ceiling=3),
    interpretation='054 optimized compilation is inside extraction, not an independent Rust test command',
    print_axioms='N/A: no new Lean declaration')
(E/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
out=dict(schema='ProverRwFactoryState-local-integrity-v1',command=sys.argv,
    source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    script_sha256=sha(Path(__file__)),wall_seconds=time.monotonic()-start,exit_status=0,
    inputs_sha256={str(p.relative_to(R)):sha(p) for p in sorted([*D.glob('*.py'),E/'emission-audit.json',E/'shape-check.json',o/'receipt.json',o/'preflight.json',o/'go-hashes.json',E/'runner-logs/outputs.json'])},
    print_axioms='N/A: read-only integrity audit; no Lean theorem',claim='packet/source/hash/cap/budget consistency only; no native/refinement/effects/security/ELF claim')
(E/'local-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS focused FactoryState packet integrity; prospective-only; native/P6/effects/finite16/outer8/E1/L1/L2/L3 open')
