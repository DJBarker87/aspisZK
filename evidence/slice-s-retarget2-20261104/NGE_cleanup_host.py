"""Remove only owned scratch whose exact bytes have retained backups."""
from pathlib import Path
import json,hashlib,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-slice-s-retarget2-20261104');C=Path('/home/dombarker/project-offloads/codex-cx-slice-s-retarget2-cache-20261104');manifest=json.loads((B/'NGE_RAW_BACKUPS.json').read_text());export=json.loads((B/'NGE_EXPORT.json').read_text());pins={r['path']:r for r in export['exports']};objects=[];graphs=[]
for p in (B/'NGE_objects').rglob('*'):
 if not p.is_file():continue
 backup=C/'NGE_exports_20261104'/p.relative_to(B/'NGE_objects');pin=pins[str(backup)];h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==pin['sha256']==hashlib.sha256(backup.read_bytes()).hexdigest();objects.append(p)
for name in ['NGE_Driver','NGE_ProofDriver']:
 p=B/'NGE_native'/name;backup=C/'NGE_native_20261104'/name;pin=pins[str(backup)];assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256']==hashlib.sha256(backup.read_bytes()).hexdigest();objects.append(p)
for r in manifest['graphs']:
 name=r['host_name'];assert name.startswith('NEP_') and name.endswith('_REACHABLE.txt') and '/' not in name
 p=B/name;assert hashlib.sha256(p.read_bytes()).hexdigest()==r['uncompressed_sha256'];graphs.append(p)
# All checks complete before the first unlink. Cache, sources, logs, keys and
# receipts are outside these explicit lists and remain retained.
for p in objects+graphs:p.unlink()
active=[]
for p in Path('/proc').glob('[0-9]*/cmdline'):
 try:args=p.read_bytes().replace(b'\0',b' ').decode(errors='replace')
 except (OSError,PermissionError):continue
 if 'S2W_run_host.py NGE_L' in args:active.append(args)
assert not active,active
out=dict(status='PASS',compiled_scratch_removed=len(objects),raw_graphs_removed=len(graphs),raw_graph_backup_revision=manifest['revision'],raw_graph_manifest_sha256=hashlib.sha256((B/'NGE_RAW_BACKUPS.json').read_bytes()).hexdigest(),retained_cache=str(C),cache_deleted=False,source_deleted=False,key_touched=False,own_prover_processes=active,disk=subprocess.check_output(['df','-h','/'],text=True),print_axioms='N/A housekeeping; no prover launch')
(B/'NGE_HOST_END.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
