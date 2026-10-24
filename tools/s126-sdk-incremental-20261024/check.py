#!/usr/bin/env python3
"""Source-only incremental release audit; optional immutable payload hashing."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,stat
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'sdk-current-incremental-20261024';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((P/'release.json').read_text());m=json.loads((P/'release-manifest.json').read_text());assert sha(P/'release-manifest.json')==r['manifest_sha256']
base=json.loads((E/'sdk-current-export-20261024/release.json').read_text());bm=json.loads((E/'sdk-current-export-20261024/release-manifest.json').read_text());assert m['base_manifest_sha256']==base['manifest_sha256'] and m['base_location']==base['location'] and m['base_transport_modules']==1287
summary=m['combined_audit'];assert summary['unresolved']==[] and summary['missing_seeds']==[] and summary['conflicts']==0 and summary['constants']==27287+m['incremental_constants']
assert m['new_transport_modules']==r['new_transport_modules'] and m['raw_unsafe_or_partial']==bm['raw_unsafe_or_partial']
assert len(m['proof_refresh'])==2 and all(x['same_type'] and x['old_theorem'] and x['new_theorem'] for x in m['proof_refresh'])
inputs=json.loads((P/'input-v2.json').read_text());pins=json.loads((P/'input-pins-v2.json').read_text());assert inputs['all_declarations']==[] and set(inputs['baseline_names'])==set(pins['baseline_names'])
assert len(pins['changes'])==1 and pins['changes'][0]['module']=='AdapterRwAccepted' and pins['changes'][0]['baseline_contains_no_constants_from_this_module']
source=json.loads((P/'accepted-proof-replay-source.json').read_text());replay=E/'sdk-current-accepted-proof-replay-v1';rr=json.loads((replay/'receipt.json').read_text());assert rr['source_sha256']==source['sha256']==sha(S/'AdapterRwAccepted.lean')==sha(replay/'source.lean')
assert hashlib.sha256(subprocess.check_output(['git','show',source['revision']+':'+source['path']],cwd=R)).hexdigest()==source['sha256']
assert rr['object_sha256']==pins['changes'][0]['new_files'][0]['sha256']
for report in rr['print_axioms']:
 a=re.findall(r'\[(.*?)\]',report,re.S);assert a and set(a[0].replace(' ','').replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
for label,row in m['ledger'].items():
 p=E/label;rec=json.loads((p/'receipt.json').read_text());assert all(rec[k]==v for k,v in row.items())
 assert rec['exit_status']==0 and rec['swaps']==0 and sha(p/'source.lean')==rec['source_sha256'] and '-j1' in rec['command'] and '-M4400' in rec['command']
for key,mod in [('generator.json','S126SdkIncrementalExportV1'),('audit-generator.json','S126SdkIncrementalAuditV1')]:
 d=json.loads((P/key).read_text());assert sha(R/d['source'])==d['source_sha256'] and sha(S/(mod+'.lean'))==d['output_sha256']
for name in ['post-export-inputs.json','post-audit-inputs.json']:
 d=json.loads((P/name).read_text());assert d['all_unchanged'] and all(x['unchanged'] for x in d['files'])
failed=json.loads((E/'sdk-current-incremental-export-v1/receipt.json').read_text());assert failed['exit_status']!=0
assert (E/'sdk-current-trace-closure-export-v1/preflight.json').is_file()
for rel,h in json.loads((P/'tool-pins.json').read_text()).items():assert sha(R/rel)==h
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
assert not any(p.stat().st_size>5_000_000 for p in P.glob('*.json'))
if '--released' in sys.argv:
 d=Path(r['location']);assert sha(d/'manifest.json')==r['manifest_sha256']
 for f in m['files']:
  p=d/f['relative'];assert p.is_file() and not p.is_symlink() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'] and stat.S_IMODE(p.stat().st_mode)&0o222==0
 assert stat.S_IMODE(d.stat().st_mode)&0o222==0
 basepath=Path(m['base_location']);assert sha(basepath/'manifest.json')==m['base_manifest_sha256']
 for f in bm['files']:
  if f['relative'].startswith('transport/'):
   p=basepath/f['relative'];assert sha(p)==f['sha256']
print(json.dumps(dict(status='PASS',incremental_constants=m['incremental_constants'],new_modules=m['new_transport_modules'],base_reused_modules=1287,combined=summary,proof_only_refresh=True,released_payload_hashed='--released' in sys.argv,scope=m['scope'])))
