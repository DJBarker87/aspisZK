"""Final local provenance/budget/hygiene checks; no compiler or prover launches."""
from pathlib import Path
import json,re,hashlib,lzma,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];J=lambda p:json.loads(p.read_text());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
required=['NFY_FAMILIES.md','NFY_RETARGET.md','NFY_PROVENANCE.json','NFY_COMBINED_IMPORT.lean','NFY_AUDIT.json','NFY_SCAN.json','NFY_LEDGER_DELTA.json','NFY_METHOD.md','NFY_HANDOFF.md','NFY_REMAINING.md','NFY_ATTEMPTS.jsonl']
assert all((E/n).is_file() for n in required)
entries=[json.loads(l) for l in (E/'NFY_ATTEMPTS.jsonl').read_text().splitlines()];charged=[r for r in entries if re.fullmatch('NFY_L[0-9]{3}',r['attempt'])];assert len(charged)==110 and {r['attempt'] for r in charged}=={f'NFY_L{i:03}' for i in range(1,111)}
normal=[J(p) for p in E.glob('NFY_L*/receipt.json')];assert len(normal)==109
caps={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in normal:
 assert r['limits']==caps and str(r['swaps'])=='0'
 ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['source_revision'] and r['source_hashes'] and r['deps_fingerprint']
 if r['kind']=='lean':assert '-M7000' in r['command']
 if r['kind']=='link':assert '-O3' in r['command']
assert J(E/'NFY_L007.json')['kind']=='own_client_collision'
raw=lzma.decompress((E/'NFY_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'NFY_CLOSURE_PINS.json.sha256').read_text().strip();assert json.loads(raw)['module_count']==13197
assert all(r.get('unchanged') for r in J(E/'NFY_LAUNCHER_PINS.json'))
assert J(E/'NFY_TESTS.json')['rejected_mutations']==25
assert len(J(E/'NFY_LEDGER_DELTA.json')['promotions'])==19 and len(J(E/'NFY_LEDGER_DELTA.json')['remaining_qualified_S'])==70
assert not list(E.rglob('__pycache__'))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
assert not [p for p in E.rglob('*') if p.is_file() and p.suffix in ['.olean','.ir','.o','.elf','.so','.a']]
for item in subprocess.check_output(['git','status','--porcelain','-z'],cwd=R).decode().split('\0'):
 if item:assert item[3:].startswith(str(E.relative_to(R))+'/'),('outside owned evidence',item)
result=dict(status='PASS',charged=110,normal_receipts=109,normal_exit0=sum(r['exit_status']==0 for r in normal),normal_exit1=sum(r['exit_status']==1 for r in normal),empty_wrapper_rejections=1,peak_rss_kib=max(int(r['peak_rss_kib']) for r in normal),swaps=0,scope_wall_seconds=sum(r['wall_seconds'] for r in normal),kani=0,extraction=0,rust=0,elf_rebuild=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,scope='Local artifact checks; no formal launch')
(E/'NFY_HYGIENE.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(result))
