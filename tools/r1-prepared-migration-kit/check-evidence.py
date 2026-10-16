#!/usr/bin/env python3
"""Hash/receipt/native trace audit only; no builds or runtime execution."""
from pathlib import Path
import hashlib,json,tarfile
ROOT=Path(__file__).resolve().parents[2];E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prepared-tx1-native-20261016'
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((E/'SUMMARY.json').read_text());archive=E/'prepared-tx1-final-native-evidence.tar.gz';assert sha(archive.read_bytes())==s['archive_sha256']
with tarfile.open(archive) as t:
 for n in ['inputs-clean.json','inputs-injected.json']:
  d=json.load(t.extractfile(n))
  for path,digest in d['files'].items():assert sha(t.extractfile(path).read())==digest,(n,path)
 for label,r in s['results'].items():
  actual=json.load(t.extractfile('runs/'+label+'/receipt.json'));assert actual==r and r['exit_status']==0
  assert r['process_swaps']==0 and r['limits']['memory.swap.max']=='0'
  assert sha(t.extractfile('runs/'+label+'/stdout.log').read())==r['stdout_sha256']
  assert sha(t.extractfile('runs/'+label+'/stderr.log').read())==r['stderr_sha256']
 for label,marker in [('prepared-failure-overlay-fixed','total=528'),('tx1-saved-s2-overlay','TX1_REAL_S2_PASS cases=5'),('tx1-shared-overlay','TX1_SHARED_PASS cases=30')]:
  assert marker in t.extractfile('runs/'+label+'/stdout.log').read().decode()
 failed=json.load(t.extractfile('runs/prepared-failure-overlay/receipt.json'));assert failed['exit_status']==101
 for path,digest in json.load(t.extractfile('runs/prepared-failure-overlay/input-manifest.json'))['files'].items():
  if path.startswith('source/'):
   saved='runs/prepared-failure-overlay/source-snapshot/'+path.removeprefix('source/')
   assert sha(t.extractfile(saved).read())==digest,saved
print(json.dumps({'status':'PASS','clean_gates':3,'prepared_cases':528,'tx1_actual_s2_cases':5,'tx1_shared_cases':30,'failed_original_inputs':'retained and hash verified','builds_executed':False}))
