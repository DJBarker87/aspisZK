"""Retain gate artifacts/keys; remove only this job's rebuildable targets."""
import pathlib,json,hashlib,shutil,subprocess,datetime
H=pathlib.Path(__file__).resolve().parent
assert H.name=='codex-pv-rebase3-20261027'
comparison=json.loads((H/'fixture-comparison.json').read_text());assert comparison['passed']
for name in ['build-default-gate','build-devnet-configured','build-pool-configured']:
 r=json.loads((H/'candidate'/name/'comparison.json').read_text());assert r['matches']
subprocess.run(['python3',str(H/'verify-host-sources.py')],check=True)
keys=json.loads((H/'key-retention.json').read_text())
for row in keys['keys']:
 p=pathlib.Path(row['path']);assert p.is_file() and p.stat().st_mode&0o777==0o600
 assert bytes(json.loads(p.read_text())[32:]).hex()==row['public_key_hex']
if (H/'cleanup.json').exists() and not (H/'cleanup-initial.json').exists():
 (H/'cleanup-initial.json').write_bytes((H/'cleanup.json').read_bytes())
removed=[];retained=[]
for name in ['native-target','sbf-target-verifier','sbf-target-pool']:
 p=H/name
 if not p.exists():continue
 assert not p.is_symlink()
 protected=[]
 for f in p.rglob('*.json'):
  try:value=json.loads(f.read_text())
  except (ValueError,UnicodeError):continue
  if f.name.endswith('-keypair.json') or (isinstance(value,list) and len(value)==64 and all(isinstance(x,int) and 0<=x<256 for x in value)):protected.append(f)
 if protected:retained.append(dict(path=str(p),reason='key-named file present',files=[str(x) for x in protected]));continue
 shutil.rmtree(p);removed.append(str(p))
record=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),removed_rebuildable_targets=removed,retained_targets=retained,retained_keys=keys['keys'],retained_artifacts='candidate/bin, research/bin, three build artifact directories, raw fixed-coin fixtures, static audit, all receipts and source snapshots',no_transactions=True,cleanup_guard='Inspect JSON contents for 64-byte key arrays; solana-keypair .rlib/.rmeta/.fingerprint metadata are compiler artifacts, not wallet material',print_axioms='N/A no Lean compilation')
(H/'cleanup.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
