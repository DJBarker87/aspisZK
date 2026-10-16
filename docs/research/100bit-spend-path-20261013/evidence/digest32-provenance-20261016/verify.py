#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,tarfile
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 d=json.loads((HERE/'manifest.json').read_text());archive=HERE/'provenance.tar.gz';assert sha(archive.read_bytes())==d['archive_sha256']
 assert sha((HERE/'source-audit.json').read_bytes())==d['source_audit_sha256']
 with tarfile.open(archive,'r:gz') as t:
  assert set(t.getnames())==set(d['files']);blobs={n:t.extractfile(n).read() for n in t.getnames()}
 for n,h in d['files'].items():assert sha(blobs[n])==h,n
 for r in d['accepted_results']:
  base=str(Path(r['receipt']).parent);receipt=json.loads(blobs[r['receipt']]);log=blobs[r['axioms_log']].decode()
  assert receipt['exit_status']==0 and receipt['process_swaps']==0
  assert receipt['limits']['memory.swap.max']=='0' and int(receipt['limits']['memory.max'])<=8*2**30
  for filename,key in [('source.lean','source_sha256'),('runner.py','runner_sha256'),('input-manifest.json','input_manifest_sha256')]:assert sha(blobs[base+'/'+filename])==receipt[key]
  reports=re.findall(r"^'[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",log,re.M);assert len(reports)==r['axioms_reports']
  for xs in reports:assert set(re.findall(r'[A-Za-z_.]+',xs)) <= {'propext','Classical.choice','Quot.sound'}
  assert 'error:' not in log and 'sorryAx' not in log
  env='begin' if r['target'].endswith('BeginProvenance') else 'prefix';name=r['target'].replace('.','/')
  assert sha(blobs[env+'/objects/'+name+'.olean'])==receipt['olean_sha256']
  assert sha(blobs[env+'/sources/'+name+'.lean'])==receipt['source_sha256']
  assert (HERE.parents[1]/'lean'/(name+'.lean')).read_bytes()==blobs[env+'/sources/'+name+'.lean']
 assert len(json.loads(blobs['prefix/separate-import-conflicts.json'])['conflicts'])==8
 print(json.dumps({'status':'PASS','archive_sha256':d['archive_sha256'],'files':len(blobs),'accepted_targets':2,'standard_only_axioms_reports':8,'scope':d['scope']},indent=2))
if __name__=='__main__':main()
