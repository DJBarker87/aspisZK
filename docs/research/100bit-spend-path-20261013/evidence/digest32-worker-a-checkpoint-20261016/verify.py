#!/usr/bin/env python3
"""Read/hash-only verification of the bounded Worker A checkpoint."""
from pathlib import Path
import hashlib,json,re,tarfile
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 d=json.loads((HERE/'manifest.json').read_text());archive=HERE/'worker-a-checkpoint.tar.gz'
 assert sha(archive.read_bytes())==d['archive_sha256']
 with tarfile.open(archive,'r:gz') as t:
  assert set(t.getnames())==set(d['files'])
  blobs={n:t.extractfile(n).read() for n in t.getnames()}
 for n,h in d['files'].items():assert sha(blobs[n])==h,n
 for r in d['accepted_results']:
  receipt=json.loads(blobs[r['receipt']]);base=str(Path(r['receipt']).parent)
  assert receipt['exit_status']==0 and receipt['process_swaps']==0
  assert receipt['limits']['memory.swap.max']=='0' and int(receipt['limits']['memory.max'])<=8*2**30
  assert sha(blobs[base+'/source.lean'])==receipt['source_sha256']
  assert sha(blobs[base+'/runner.py'])==receipt['runner_sha256']
  assert sha(blobs[base+'/input-manifest.json'])==receipt['input_manifest_sha256']
  log=blobs[r['axioms_log']].decode();assert 'error:' not in log and 'sorryAx' not in log
  reports=re.findall(r"^'[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",log,re.M)
  assert len(reports)==r['axioms_reports']
  for xs in reports:assert set(re.findall(r'[A-Za-z_.]+',xs)) <= {'propext','Classical.choice','Quot.sound'}
  name=receipt['target'].replace('.','/')
  assert sha(blobs['c16/lean/objects/'+name+'.olean'])==receipt['olean_sha256']
  assert sha(blobs['c16/lean/sources/'+name+'.lean'])==receipt['source_sha256']
  assert (HERE.parents[1]/'lean'/(name+'.lean')).read_bytes()==blobs['c16/lean/sources/'+name+'.lean']
 for n in ['c16/PublicPreparation.llbc','pre-unroll/PublicPreparation-restored-a.llbc']:
  assert json.loads(blobs[n])['has_errors'] is False
 for n in d['rejected_native_llbc']:assert json.loads(blobs['full-native-rejected/'+n])['has_errors'] is True
 pins=json.loads(blobs['c16/lean/named-current-import-pins.json'])
 for mod,pin in pins.items():
  stem=mod.replace('.','/')
  assert sha(blobs['c16/lean/sources/'+stem+'.lean'])==pin['source_sha256']
  assert sha(blobs['c16/lean/objects/'+stem+'.olean'])==pin['object_sha256']
  assert sha(blobs['c16/lean/producing-import-receipts/'+mod+'.json'])==pin['receipt_sha256']
 print(json.dumps({'status':'PASS','archive_sha256':d['archive_sha256'],'files':len(blobs),'accepted_targets':len(d['accepted_results']),'axioms_reports':sum(x['axioms_reports'] for x in d['accepted_results']),'scope':d['scope']},indent=2))
if __name__=='__main__':main()
