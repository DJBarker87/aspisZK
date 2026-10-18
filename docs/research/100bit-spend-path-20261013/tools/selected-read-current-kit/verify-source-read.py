#!/usr/bin/env python3
"""Read/hash the two checked source bridges; never launch a compiler."""
from pathlib import Path
import tarfile,json,hashlib
ROOT=Path(__file__).resolve().parents[2];E=ROOT/'evidence/source-read-current-20261018';m=json.loads((E/'packet-manifest.json').read_text());p=E/m['archive'];sha=lambda b:hashlib.sha256(b).hexdigest();assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==m['archive_sha256']
with tarfile.open(p) as t:
 sums=json.load(t.extractfile('SHA256SUMS.json'));assert set(t.getnames())==set(sums)|{'SHA256SUMS.json'}
 for n,h in sums.items():assert hashlib.file_digest(t.extractfile(n),'sha256').hexdigest()==h,n
 load=lambda n:json.load(t.extractfile(n));get=lambda n:t.extractfile(n).read();rs=[load(n) for n in sums if n.startswith('successful-targets/')];manifest=load('sources/SOURCE-MANIFEST.json')
 assert len(rs)==2 and sum(len(r['axioms']['reports']) for r in rs)==10
 for r in rs:
  assert r['exit_status']==0 and r['axioms']['passed'] and r['process_swaps']==0
  assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['axioms']['reports'])
  assert r['key']['source_sha256']==sha(get('sources/'+manifest['modules'][r['target']]['stage_as']))
  assert r['key']['source_sha256']==sha((ROOT/'lean/bridge-selected-current-20261018'/manifest['modules'][r['target']]['stage_as']).read_bytes())
  for suffix,v in r['objects'].items():assert sums['objects/'+r['target']+suffix]==v['sha256']
  pin=load('runs/source-read-'+r['target']+'-'+('4' if r['target']=='ExtractedSourceSemanticSampler' else '1')+'/'+r['target']+'/shared-lock.json');assert pin['outcome']=='acquired' and pin['released_utc']
 d=load('external-inputs.json');assert len(d['modules'])==6110
 audit=load('coherent-import-merge-audit.json');assert audit['common_module_count']==5676 and audit['fresh_selected_project_count']==215 and audit['recursive_producing_import_identity_checked']
 for n,v in d['modules'].items():assert any(root['name']==v['root'] for root in d['roots']),n
 source=get('sources/ExtractedSelectedSourceRecords.lean').decode();assert 'completed_read_of_decode' in source and 'ActualFull25.first_full25' in source
 assert 'actual completed q agreement' in m['scope']
print('PASS2 current source bridges /10standard reports; current215+sampler coherent imports, explicit oracle/callback scope; no compiler invoked')
