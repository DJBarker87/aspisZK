#!/usr/bin/env python3
"""Read-only archive/source/statement audit; no build or proof replay."""
from pathlib import Path
import hashlib,json,subprocess,sys,tarfile,tempfile
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
expected={'queries-current-emission.tar.gz':'ca749c0ca3a6ebcddc5ae29c552b566bbcf195381c16b5b027c301b7bcf56483','query-enumeration-failure.tar.gz':'75edd80d2d39dedceece893881c79df7bd88c697f4bc748777fe0a5b4d791603','query-model-proof.tar.gz':'31863f82b0f3d3b2fe0f806addaf83ed133e9e4b86d25209d126085f14a2525b'}
for n,h in expected.items():assert sha((E/n).read_bytes())==h,n
with tempfile.TemporaryDirectory(prefix='queries-check-')as tmp:
 out=Path(tmp)
 with tarfile.open(E/'queries-current-emission.tar.gz')as t:
  rawpins=t.extractfile('input/source-pins.json').read();pins=json.loads(rawpins);kit=BASE/'tools/callers-current-extraction-kit/queries';normalized=json.loads((kit/'source-pins.json').read_text());assert (kit/'producing-source-pins.json').read_bytes()==rawpins
  assert sha((kit/'base52/source-pins.json').read_bytes())==pins['base52_source_pins_sha256']=='389b09c9f9411403cff9a97062c8f8b120e7e75dd7605c7bb6757e9033725361'
  for name,digest in normalized['kit_files'].items():assert sha((kit/name).read_bytes())==digest,name
  lib=t.extractfile('input/lib.rs').read()
  for n,h in pins['kit_files'].items():assert sha(t.extractfile('input/'+n).read())==h,n
  for c in pins['cuts']+pins['base52_cuts']:
   src=subprocess.check_output(['git','-C',str(ROOT),'show',pins['revision']+':'+c['path']]);span=src[c['start_byte']:c['end_byte_exclusive']];assert sha(span)==c['sha256'],c['name'];assert span in lib,c['name']
  llbc=json.load(t.extractfile('VerifyPreparedPrefix.llbc'));assert not llbc['has_errors']
  for phase in ['charon-b','aeneas-b']:assert json.load(t.extractfile('runs/'+phase+'/receipt.json'))['exit_status']==0
  for n in ['Types.lean','Funs.lean']:(out/n).write_bytes(t.extractfile('generated/AspisR1PublicPreparation/'+n).read())
 subprocess.run([sys.executable,str(BASE/'tools/callers-current-extraction-kit/bind-queries.py'),'--generated',str(out),'--out',str(BASE/'lean/bridge-opening-queries-1b98-20261017'),'--check'],check=True)
with tarfile.open(E/'query-model-proof.tar.gz')as t:
 r=json.load(t.extractfile('lean/runs/query-model-a/receipt.json'));assert r['exit_status']==0
 assert sha((BASE/'lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean').read_bytes())==r['source_sha256']
 log=t.extractfile('lean/runs/query-model-a/lean.log').read().decode();assert 'sorryAx'not in log and log.count('depends on axioms:')==2
print(json.dumps({'status':'PASS','LLBC_valid':True,'copied_current_source_cuts':len(pins['cuts'])+len(pins['base52_cuts']),'bound_definition_axiom_reports':2,'opaque_template_imported':False,'builds_executed':False}))
