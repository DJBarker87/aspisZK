"""Final read-only evidence checks in own admitted scopes; no proof replay."""
from pathlib import Path
import json,lzma,hashlib,shutil,sys,os
B=Path.cwd();mode=sys.argv[1];H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(B/n).write_text(json.dumps(x,indent=2)+'\n')
if mode=='retention':
 # L122 walker completed; only its packaging timed out. No proof replay.
 for p in B.glob('NEP_proof14_*'):
  if p.is_file():
   raw=p.read_bytes();q=B/'NLR_audit/proof14'/(p.name+'.xz');q.write_bytes(lzma.compress(raw,preset=0));Path(str(q)[:-3]+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 closure=json.loads(lzma.decompress((B/'NLR_CLOSURE_PINS.json.xz').read_bytes()))
 for x in closure['selected_objects']:assert H(Path(x['path']))==x['sha256'],x['path']
 exports=json.loads((B/'NLR_EXPORT.json').read_text())
 for x in exports['files']:assert H(Path(x['path']))==x['sha256']
 for x in json.loads((B/'NLR_PROOF_SOURCE.json').read_text())['sources']:assert H(Path(x['path']))==x['sha256']
 text_checks=0
 for p in (B/'NLR_audit').rglob('*.xz'):
  raw=lzma.decompress(p.read_bytes());q=Path(str(p)[:-3]+'.sha256')
  assert q.is_file()and hashlib.sha256(raw).hexdigest()==q.read_text().strip(),str(p)
  text_checks+=1
 pins={**json.loads((B/'NLR_SOURCE_PINS.json').read_text()),**json.loads((B/'NLR_FROZEN_FILE_PINS.json').read_text())}
 assert all(H(B/'NLR_src'/n)==v for n,v in pins.items())
 own=sum(p.stat().st_size for p in B.rglob('*')if p.is_file());assert own<30_000_000_000
 x=dict(status='PASS',selected_objects=len(closure['selected_objects']),export_files=len(exports['files']),compressed_sha_pairs=text_checks,native_source_pins=len(pins),own_host_bytes=own,disk=shutil.disk_usage(B)._asdict(),target_dir=os.environ['CARGO_TARGET_DIR'],deletions=0)
 write('NLR_RETENTION.json',x)
elif mode=='audit':
 standard={'propext','Classical.choice','Quot.sound'};roots=[];mismatches=[];groups=[]
 for j in range(30):
  p=B/'NLR_audit'/('proof'+str(j))/('proof'+str(j)+'.json');r=json.loads(p.read_text());groups.append(r)
  for v in r['results']:
   assert set(v['walked_axioms'])<=standard,v
   roots.append(v['root'])
   if not v['equal']:mismatches.append(v)
 expected=json.loads((B/'NLR_AUDIT_ROOTS.json').read_text())['roots'];assert sorted(roots)==sorted(expected)
 scan=[json.loads(l)for l in(B/'NLR_LOADED_scan.jsonl').read_text().splitlines()]
 assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 fixtures=json.loads((B/'NLR_audit/fixtures/fixtures.json').read_text());assert len(fixtures['results'])==8 and all(r['equal']for r in fixtures['results'])
 comparison=json.loads((B/'NLR_PREDECESSOR_COMPARISON.json').read_text());assert all(r['status']=='PASS'for r in comparison.values())
 rc=lambda a:json.loads((B/a/'receipt.json').read_text())
 x=dict(status='PASS_STANDARD_RAW_WITH_RETAINED_COLLECTOR_DISAGREEMENTS'if mismatches else'PASS',target_established=False,headline='AspisR1.RPx_Deployed.deployed',combined_audits=1,combined_import=rc('NLR_L101'),nfx=rc('NLR_L107'),scan_modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,raw_roots=len(roots),raw_groups=[dict(target=r['target'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],rss=r['peak_rss_kib'],swaps=r['swaps'])for r in groups],raw_all_standard=True,collector_disagreements=mismatches,fixtures=fixtures,predecessor_comparison=comparison,schemas_source_value_only=True,full_child136_packet=False,closed_rows=[],candidate_roots=[],kani_budget_used=40,lean_support_charged_including_this_scope=140,extraction_used=0)
 # Receipt fingerprints are already retained individually; do not repeat multi-MB deps here.
 for key in ['combined_import','nfx']:x[key]={k:v for k,v in x[key].items()if k!='deps_fingerprint'}
 write('NLR_GATE_AUDIT.json',x)
 x={k:v for k,v in x.items()if k not in ['combined_import','nfx','fixtures','predecessor_comparison','raw_groups','collector_disagreements']}
else:raise AssertionError(mode)
print(json.dumps(x))
