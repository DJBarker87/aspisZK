from pathlib import Path
import json,hashlib,lzma,sys,re
b=Path.cwd();a=sys.argv[1];d=b/'PCC_closure';raw=lzma.decompress((d/'PCC_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(d/'PCC_CLOSURE_PINS.json.sha256').read_text().strip()
manifest=json.loads(raw)
roots=json.loads((b/'PCC_ROOT_MANIFEST.json').read_text());assert not roots['pool_row_roots']
scan=[json.loads(l) for l in (b/'PCC_final_audits/PCC_L068/PCC_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling'] and r['imports_match'] for r in scan)
binary_hashes=[]
for i in [66,67,68]:
 r=json.loads((b/f'PCC_L{i:03d}/receipt.json').read_text());assert r['exit_status']==0
 receipt=json.loads((b/f'PCC_final_audits/PCC_L{i:03d}/PCC_binary.json').read_text());assert receipt['before']==receipt['after'] and receipt['exit']==0
 binary_hashes.append(receipt['before'])
assert len(set(binary_hashes))==1
for r in roots['all_roots']:
 p=b/'PCC_final_audits/PCC_L067'/('NEP_proof0_'+r+'_REACHABLE.txt');assert p.is_file(),r
# Every ordinary printed axiom line in the root audit must name standard axioms only.
stdout=(b/'PCC_L067/stdout.log').read_text()
assert 'sorryAx' not in stdout
allowed={'propext','Classical.choice','Quot.sound'}
for line in stdout.splitlines():
 if 'depends on axioms:' in line:
  names=line.rsplit('[',1)[1].split(']',1)[0];assert set(n.strip() for n in names.split(',') if n.strip())<=allowed,line
for r in json.loads((b/'PCC_CURRENT_INPUTS.json').read_text())['modules'].values():assert hashlib.sha256((b/r['source']).read_bytes()).hexdigest()==r['sha256']
out=dict(status='PASS_SUPPORT_ONLY',raw_roots=len(roots['all_roots']),new_theorems=len(roots['new_theorems']),scan_modules=len(scan),objects_pinned=len(manifest['objects']),binary_identical_across_fixtures_raw_scan=True,nonstandard_axioms=0,pool_rows_closed=0)
(b/(a+'-source-retention.json')).write_text(json.dumps(out,indent=1)+'\n');print('Support gate retention rechecked; zero Pool row roots or promotions')
