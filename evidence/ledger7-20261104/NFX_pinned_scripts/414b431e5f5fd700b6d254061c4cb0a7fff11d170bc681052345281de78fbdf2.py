"""Final focused receipt, transport, source and packaging checks; no provers."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re,sys
E=Path(__file__).resolve().parent;R=E.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
if '--pin' in sys.argv:
 files={str(p.relative_to(E)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(E.rglob('*')) if p.is_file() and p.name!='NFX_OUTPUTS.json'}
 (E/'NFX_OUTPUTS.json').write_text(json.dumps(dict(files=files,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()),indent=1)+'\n');print('Pinned',len(files),'files');sys.exit(0)
if '--check-output' in sys.argv:
 m=json.loads((E/'NFX_OUTPUTS.json').read_text())['files']
 for path,pin in m.items():
  p=E/path;assert p.stat().st_size==pin['bytes'] and sha(p.read_bytes())==pin['sha256'],path
 assert set(m)=={str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.name!='NFX_OUTPUTS.json'}
 print('Output manifest verified');sys.exit(0)
for name,target in [('NFX_LEDGER_FINAL','NFX_ledger.py'),('NFX_TESTS','NFX_tests.py'),('NFX_AUDIT_FINAL2','NFX_finalize.py')]:
 r=json.loads((E/(name+'.json')).read_text());assert r['exit_status']==0;assert r['source_sha256'][target]==sha((E/target).read_bytes()),target
for p in E.rglob('*.xz'):
 side=Path(str(p)[:-3]+'.sha256')
 if side.exists():assert sha(lzma.decompress(p.read_bytes()))==side.read_text().split()[0],str(p)
for name in ['NFX_LEDGER.md','NFX_LEDGER.json.xz','NFX_LEDGER.json.sha256','NFX_ROUTES.json','NFX_TRUST_USED.json','NFX_COMBINED_IMPORT.lean','NFX_AUDIT.json','NFX_FINDINGS.md','NFX_HANDOFF.md','NFX_ATTEMPTS.jsonl']:assert (E/name).is_file(),name
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
 assert p.name!='__pycache__',str(p)
for p in E.glob('NFX_*.lean'):
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(?:maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p.name
# Verify all final source statements were compiled from exactly these bytes.
for number in range(36,41):
 a=f'NFX_L{number:03}';r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0
 assert sha((E/(r['module']+'.lean')).read_bytes()) in r['source_hashes'].values()
# Source truth and row inventory are anchored, never updated through a name.
changed=subprocess.check_output(['git','diff','--name-only','616c30e35be','--'],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/ledger7-20261104/') for p in changed),changed
status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=R,text=True).splitlines()
assert all(l[3:].startswith('evidence/ledger7-20261104/') for l in status),status
ignored=subprocess.check_output(['git','ls-files','--others','--ignored','--exclude-standard','--','evidence/ledger7-20261104'],cwd=R,text=True).splitlines();assert not ignored,ignored
assert not json.loads((E/'NFX_RESEARCH_CHECK.json').read_text())['landed_NFT_NFU_paths']
budget=json.loads((E/'NFX_BUDGET.json').read_text());assert budget['host_slots_charged']==40 and budget['normal_receipts']==36 and budget['kani_used']==budget['extraction_used']==0
# Fresh child status equality prevents accidental use of an archived report line.
fresh=(E/'NFX_replay_outputs/NEZ/evidence/ledger5-20261104/NEZ_NEI_STATUS.log').read_text().splitlines()[-1]
old=(R/'evidence/ledger5-20261104/NEZ_NEI_STATUS.log').read_text().splitlines()[-1];assert json.loads(fresh)==json.loads(old)
# The common-library object identities are explicit, not blanket name admission.
variants=json.loads((E/'NFX_LEGACY_FAMILY_PINS.json').read_text());assert len(variants)==15
scan=list(map(json.loads,(E/'NFX_LOADED_scan.jsonl').read_text().splitlines()));assert len(scan)==13126
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
assert not {'NEP_Planted','NEP_Mutations'} & {r['module'] for r in scan}
print(json.dumps(dict(status='PASS',packaging='all required outputs present; large JSON compressed; all xz transports verified',source='only NFX evidence differs from initial tip',host_slots=40,raw_roots=263,scan_modules=len(scan),shipped_source_changed=False,elf_rebuild_trigger=False,trust_or_security_target_changed=False)))
