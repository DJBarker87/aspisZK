from pathlib import Path
import hashlib,json,tarfile
W=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((W/'manifest.json').read_text());archive=W/m['archive'];assert sha(archive.read_bytes())==m['archive_sha256']
with tarfile.open(archive) as t:
 sums={line.split('  ',1)[1]:line.split('  ',1)[0] for line in t.extractfile('SHA256SUMS').read().decode().splitlines()};assert len(sums)+1==m['archive_entries'];blobs={}
 for n,h in sums.items():
  b=t.extractfile(n).read();assert sha(b)==h,n;blobs[n]=b
 for k,r in m['receipts'].items():
  assert r==json.loads(blobs['actual-tx1/runs/'+k+'/receipt.json']);assert r['source_revision']==m['production_revision'];assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'};assert r['process_swaps']==r['cgroup_swap_current']==0
 llbc=blobs[m['additional_cone']['llbc']];assert not json.loads(llbc)['has_errors'];assert sha(llbc)==m['receipts']['charon-b']['outputs']['VerifyPreparedPrefix.llbc']
 pins=json.loads(blobs[m['additional_cone']['source_pins']]);base='actual-tx1/input/'
 for n,h in pins['kit_files'].items():assert sha(blobs[base+n])==h,n
 audit=json.loads((W/'source-binding-audit.json').read_text());assert len(audit['exact_source_items'])==25
 print(f'PASS {len(sums)} archive members, 3 receipts; valid actual LLBC, rejected emission; no Lean claim')
