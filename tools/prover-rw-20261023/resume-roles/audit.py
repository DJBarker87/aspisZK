"""One focused read-only packet audit. No compiler, Kani, backend or extractor."""
from pathlib import Path
import hashlib,json,runpy,subprocess
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/resume-roles'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
observed=json.loads((E/'association.json').read_text())
expected=runpy.run_path(str(D/'inspect.py'))['inspect']()
assert observed==expected
assert not observed['native_projection_proved']
diag=json.loads((E/'readonly/diagnostic.json').read_text())
assert diag['requested_bytes']==2*2**30 and not diag['allowed']
assert diag['projected_reserved_bytes']<55*2**30
assert diag['projected_reserved_bytes']+diag['uncapped_resident_reserve_bytes']+7*2**30>=diag['meminfo']['MemTotal']
assert diag['compiler_invocations']==0
source=json.loads((E/'current-source.json').read_text())
for p,v in source['files'].items():assert sha(ROOT/p)==v['sha256']
for p,v in source['prior_packet_sha256'].items():assert sha(ROOT/p)==v
changed=subprocess.check_output(['git','diff','--name-only','8bd72836ffdab0818b01623a078913f35cd95722'],cwd=ROOT,text=True).splitlines()
assert all('/resume-roles/' in p for p in changed),changed
for p in [*D.rglob('*'),*E.rglob('*')]:
    if p.is_file():
        assert p.suffix not in ['.olean','.o','.rlib','.rmeta','.elf','.pyc'],p
        if p.suffix=='.json':assert p.stat().st_size<=5_000_000,p
print(json.dumps(dict(schema='ProverRwResumeRoles-focused-audit-v1',exit_status=0,
    source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    source_and_dependency_hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted([p for p in D.rglob('*') if p.is_file()]+[p for p in E.rglob('*') if p.is_file() and p.name not in ['audit.stdout','audit.time','audit-receipt.json']])},
    tool='read-only Python '+subprocess.check_output(['python3','--version'],text=True).strip(),
    sysroot='N/A: no Rust or Lean compilation',objects='N/A: no new objects',
    axioms='N/A: no new Lean declarations; no axioms audit invoked',
    new_invocations=dict(Lean=0,Kani=0,Rust=0,extraction=0,backend=0,ELF=0),
    result='reused success successor/move/glue and current source pins verified; read-only admission denial retained; native projection unproved'),indent=2))
