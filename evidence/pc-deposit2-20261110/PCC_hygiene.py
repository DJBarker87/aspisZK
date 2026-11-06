from pathlib import Path
import json,lzma,hashlib,shutil,subprocess
E=Path(__file__).resolve().parent
for p in E.rglob('*.log'):
 raw=p.read_bytes();p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
for p in list(E.rglob('__pycache__')):shutil.rmtree(p)
pairs=0
for p in E.rglob('*.sha256'):
 original=Path(str(p)[:-len('.sha256')]);archive=Path(str(original)+'.xz')
 if archive.exists():assert hashlib.sha256(lzma.decompress(archive.read_bytes())).hexdigest()==p.read_text().strip(),str(p);pairs+=1
index=json.loads((E/'PCC_INPUTS.json').read_text())
for h,r in index['objects'].items():
 p=E/r['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['archive_sha256'];assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==h
attempts=[json.loads(l) for l in (E/'PCC_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(attempts)==70
for r in attempts:
 a=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert a['exit']==0 and a['reservation']['allowed'] is True
 assert r['swaps']=='0' or r['swaps']==0
 assert r['limits']['MemoryMax']=='8G' if 'MemoryMax' in r['limits'] else True
 assert r['source_revision'] and r['source_hashes']
files=[p for p in E.rglob('*') if p.is_file()];assert not [p for p in files if p.stat().st_size>20_000_000]
assert not any(p.suffix in ['.olean','.elf','.o','.so','.a','.crate'] for p in files)
base=subprocess.check_output(['git','rev-parse','9180599d2e8^'],text=True).strip();changed=subprocess.check_output(['git','diff','--name-only',base,'HEAD'],text=True).splitlines();assert all(n.startswith('evidence/pc-deposit2-20261110/') for n in changed)
assert subprocess.run(['git','diff','--quiet',base,'HEAD','--','evidence/pc-deposit-pilot-20261110']).returncode==0
out=dict(status='PASS',files=len(files),largest_file_bytes=max(p.stat().st_size for p in files),xz_sha_pairs=pairs,archived_inputs=len(index['objects']),formal_attempts=70,kani_attempts=0,all_actual_admissions_exit0_allowed_true=True,oversized_files=0,compiled_binaries_committed=0,pycache_directories=0,only_job_evidence_changed=True,pca_sources_unchanged=True)
(E/'PCC_HYGIENE.json').write_text(json.dumps(out,indent=1)+'\n')
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
print('Evidence hygiene PASS:70 admitted scopes,hashes/sizes verified,no binaries or pycache')
