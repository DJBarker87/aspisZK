#!/usr/bin/env python3
"""Read-only focused proof/producing-input audit. No compiler or runtime run."""
from pathlib import Path
import hashlib,json,re,tarfile
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();s=json.loads((E/'SUMMARY.json').read_text());archive=E/'opening-circle-current-proof.tar.gz';assert sha(archive.read_bytes())==s['archive_sha256']
with tarfile.open(archive)as t:
 for target,attempt,count in [('ExtractedOpeningCalls','opening-calls-a',5),('ExtractedOpeningQueriesReachability','query-carry-a',1),('ExtractedCircleCalls','circle-calls-b',6),('ExtractedOpeningRun','opening-run-a',4)]:
  r=json.load(t.extractfile('runs/'+attempt+'/receipt.json'));assert r==s['results'][target]and r['exit_status']==0 and r['process_swaps']==0 and r['limits']['memory.swap.max']=='0';src=t.extractfile('sources/'+target+'.lean').read();assert sha(src)==r['source_sha256']==sha((BASE/'lean'/(target+'.lean')).read_bytes());log=t.extractfile('runs/'+attempt+'/lean.log').read().decode();assert 'sorryAx'not in log and 'error('not in log and ': error:'not in log;assert log.count('depends on axioms:')==count
  m=json.load(t.extractfile('runs/'+attempt+'/input-manifest.json'));assert sha(t.extractfile('runs/'+attempt+'/input-manifest.json').read())==r['input_manifest_sha256']
  for name,pin in m['current_canonical_and_begin_pins'].items():assert sha(t.extractfile('sources/'+name.replace('.','/')+'.lean').read())==pin['source_sha256']
 for name,meta in m['current_finish_import_closure'].items():
  if meta['root'] in ['backend','runtime','mathlib','aesop','batteries','Qq','proofwidgets','plausible','LeanSearchClient','importGraph']:continue
  assert sha(t.extractfile('sources/'+name.replace('.','/')+'.lean').read())==meta['source_sha256'],name
  raw=t.extractfile('producing-inputs/c-finish-'+name+'.json').read();assert sha(raw)==meta['build_receipt']['sha256'];r=json.loads(raw);assert r['exit_status']==0
  assert (r['objects']['.olean']['sha256']if 'objects'in r else r['olean_sha256'])==meta['objects']['.olean']['sha256'],name
 failed=json.load(t.extractfile('runs/circle-calls-a/receipt.json'));assert failed['exit_status']==1;assert sha(t.extractfile('runs/circle-calls-a/source-snapshot/ExtractedCircleCalls.lean').read())==failed['source_sha256']
 reservation=json.load(t.extractfile('opening-run-reservation.json'));assert reservation['current_sum']+reservation['next_worker_cap']<reservation['safe_limit']
print(json.dumps({'status':'PASS','focused_targets':4,'standard_axiom_reports':16,'current_finish_imports':len(m['current_finish_import_closure']),'failed_input_retained':True,'builds_executed':False}))
