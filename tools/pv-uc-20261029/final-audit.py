"""Final read-only source/artifact binding; no rebuild, key access or replay."""
from pathlib import Path
import hashlib,json,time

H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029')
expected=H/'final-audit-expected.json'
x=json.loads(expected.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
def check(p,want,kind):
 actual=sha(p)
 checks.append(dict(path=str(p),kind=kind,expected=want,actual=actual,match=actual==want))
for path,want in x['production_sources'].items():check(H/'src'/path,want,'production source')
for name,pin in x['client_pins'].items():check(Path(pin['path']),pin['sha256'],'final optimized executable')
for name,want in x['audit_pins'].items():check(H/'native-target/client'/name,want,'unchanged differential executable')
for mode,want in x['elf_pins'].items():
 name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'
 check(H/f'final-gates/elf-{mode}'/name,want,'release ELF; checksum only')
summary=json.loads((H/'final-gates/differential/summary.json').read_text())
assert summary['passed'] is True and summary['pairs']==1000 and summary['fully_executed_prover_calls']==2000
record=dict(utc=time.time(),expected_manifest_sha256=sha(expected),
    revision=x['revision'],checks=checks,all_match=all(c['match'] for c in checks),
    differential=summary,mode='read-only final binding; successful unchanged gates reused, never replayed',
    axioms='N/A native checks; final Lean audit separately reported',
    source_obligations='E1/E2, V370/V371, RunJoin, native I/O/formatting association and whole-client L1/L2/L3 retained; no privacy premise removed')
(H/'final-gates/final-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(all_match=record['all_match'],checks=len(checks),pairs=summary['pairs'])))
assert record['all_match'],[c for c in checks if not c['match']]
