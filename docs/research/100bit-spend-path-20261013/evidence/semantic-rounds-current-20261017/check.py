#!/usr/bin/env python3
"""Read-only source, emission, binding and focused receipt audit; no builds."""
from pathlib import Path
import hashlib,json,subprocess,sys,tarfile,tempfile
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();summary=json.loads((E/'SUMMARY.json').read_text())
for n,h in summary['archives'].items():assert sha((E/n).read_bytes())==h,n
with tempfile.TemporaryDirectory(prefix='rounds-check-')as temp:
 out=Path(temp)
 with tarfile.open(E/'rounds-current-emission.tar.gz')as t:
  pins=json.load(t.extractfile('input/source-pins.json'));lib=t.extractfile('input/lib.rs').read();kit=BASE/'tools/callers-current-extraction-kit/semantic'
  assert (kit/'source-pins.json').read_bytes()==t.extractfile('input/source-pins.json').read()
  for n,h in pins['kit_files'].items():assert sha(t.extractfile('input/'+n).read())==h and sha((kit/n).read_bytes())==h,n
  for c in pins['cuts']+pins['base52_cuts']:
   src=subprocess.check_output(['git','-C',str(ROOT),'show',pins['revision']+':'+c['path']]);span=src[c['start_byte']:c['end_byte_exclusive']];assert ('source_file_sha256'not in c or sha(src)==c['source_file_sha256']) and sha(span)==c['sha256'] and span in lib,c['name']
  assert not json.load(t.extractfile('VerifyPreparedPrefix.llbc'))['has_errors']
  for phase in ['charon-a','aeneas-a']:
   r=json.load(t.extractfile('runs/'+phase+'/receipt.json'));assert r['exit_status']==0 and r['process_swaps']==0 and r['limits']['memory.swap.max']=='0'
  for name in ['Types.lean','Funs.lean']:(out/name).write_bytes(t.extractfile('generated/AspisR1PublicPreparation/'+name).read())
 subprocess.run([sys.executable,str(BASE/'tools/callers-current-extraction-kit/bind-rounds.py'),'--generated',str(out),'--out',str(BASE/'lean/bridge-semantic-rounds-a555-20261017'),'--check'],check=True)
with tarfile.open(E/'rounds-current-proof.tar.gz')as t:
 for attempt,source in [('model-d',BASE/'lean/bridge-semantic-rounds-a555-20261017/ExtractedSemanticRoundsModel.lean'),('reach-d',BASE/'lean/ExtractedSemanticRoundsReachability.lean')]:
  r=json.load(t.extractfile('runs/'+attempt+'/receipt.json'));assert r['exit_status']==0 and r['process_swaps']==0 and r['limits']['memory.swap.max']=='0';assert sha(source.read_bytes())==r['source_sha256'];log=t.extractfile('runs/'+attempt+'/lean.log').read().decode();assert 'sorryAx'not in log and log.count('depends on axioms:')==3;assert 'error('not in log and ': error:'not in log
 assert t.extractfile('runs/reach-c/source-snapshot/ExtractedSemanticRoundsReachability.lean').read()!= (BASE/'lean/ExtractedSemanticRoundsReachability.lean').read_bytes()
print(json.dumps({'status':'PASS','source_cuts':len(pins['cuts'])+len(pins['base52_cuts']),'LLBC_valid':True,'formal_targets':2,'standard_axiom_reports':6,'opaque_globals':False,'builds_executed':False}))
