from pathlib import Path
import hashlib,json,tomllib
W=Path('/home/dombarker/project-offloads/aspis-r1-j1a-readonly-account-20261016')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
text=(W/'runs/metadata-a/stdout.log').read_text();metadata=json.loads(next(l for l in text.splitlines() if l.startswith('{"packages"')))
seed=tomllib.loads((W/'Cargo.lock.seed').read_text())['package'];selected=tomllib.loads((W/'input/Cargo.lock').read_text())['package']
old={(p['name'],p['version'],p.get('source')):p for p in seed};rows=[];file_count=0
for p in metadata['packages']:
 if not p.get('source'):continue
 key=(p['name'],p['version'],p['source']);assert key in old,key
 lock=next(v for v in selected if (v['name'],v['version'],v.get('source'))==key)
 assert lock['checksum']==old[key]['checksum']
 src=Path(p['manifest_path']).parent;checks=json.loads((src/'.cargo-checksum.json').read_text());assert checks['package']==lock['checksum']
 for rel,h in checks['files'].items():assert sha(src/rel)==h,(p['name'],rel);file_count+=1
 rows.append({'name':p['name'],'version':p['version'],'checksum':lock['checksum'],'source_dir':str(src),'manifest_sha256':sha(src/'Cargo.toml'),'checksum_manifest_sha256':sha(src/'.cargo-checksum.json'),'verified_files':len(checks['files'])})
features={p['name']:next(n['features'] for n in metadata['resolve']['nodes'] if n['id']==p['id']) for p in metadata['packages'] if p['name'] in ['solana-account-info','solana-pubkey','solana-program-error']}
expected={'solana-account-info':'2.3.0','solana-pubkey':'2.4.0','solana-program-error':'2.2.2'}
for n,v in expected.items():assert next(p['version'] for p in metadata['packages'] if p['name']==n)==v
out={'source_revision':'b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c','selected_lock_sha256':sha(W/'input/Cargo.lock'),'seed_lock_sha256':sha(W/'Cargo.lock.seed'),'all_selected_versions_and_checksums_equal_seed':True,'packages':rows,'sdk_features':features,'verified_source_files':file_count,'metadata_sha256':sha(W/'runs/metadata-a/stdout.log')}
(W/'dependency-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'packages':len(rows),'source_files':file_count,'sdk_features':features,'selected_lock_sha256':out['selected_lock_sha256']},indent=2))
