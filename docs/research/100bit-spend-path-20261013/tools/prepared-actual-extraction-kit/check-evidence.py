#!/usr/bin/env python3
"""Read/hash deterministic source and body audit; never runs Lean or Rust."""
from pathlib import Path
import hashlib,json,subprocess,sys,tarfile,tempfile
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
summary=json.loads((BASE/'evidence/prepared-actual-20261016/SUMMARY.json').read_text());archive=BASE/'evidence/prepared-actual-20261016/actual-prepared-evidence.tar.gz'
assert sha(archive.read_bytes())==summary['archive_sha256']
subprocess.run([sys.executable,str(HERE/'prepare.py'),'--base-kit',str(HERE/'input/base52'),'--out',str(HERE/'input'),'--check'],check=True)
with tempfile.TemporaryDirectory(prefix='prepared-audit-') as tmp:
 t=Path(tmp)
 with tarfile.open(archive) as f:
  for n in ['Types.lean','Funs.lean']:
   (t/n).write_bytes(f.extractfile('generated/AspisR1PublicPreparation/'+n).read())
  assert sha(f.extractfile('VerifyPreparedPrefix.llbc').read())=='3c628bdcf8ce8e580367db17bf30b052b9d30028e606fa36c0e3888472ac91e6'
  for phase in ['charon-actual-a','aeneas-actual-a']:
   receipt=json.load(f.extractfile('runs/'+phase+'/receipt.json'));assert receipt['exit_status']==0
  receipt=json.load(f.extractfile('lean/runs/reach-d/receipt.json'));assert receipt['exit_status']==0
  proof=BASE/'lean/ExtractedPreparedReachability.lean';assert sha(proof.read_bytes())==receipt['source_sha256']
  log=f.extractfile('lean/runs/reach-d/lean.log').read().decode();assert 'sorryAx' not in log and 'Quot.sound' in log
 subprocess.run([sys.executable,str(HERE/'bind.py'),'--generated',str(t),'--out',str(BASE/'lean/bridge-prepared-3335-20261016'),'--check'],check=True)
print(json.dumps({'status':'PASS','accepted_formal_target':'ExtractedPreparedReachability','llbc_valid':True,'external_template_imported':False,'six_boundaries':'explicit function arguments; no opaque global axiom'}))
