#!/usr/bin/env python3
"""Verify source, attempt receipts and standard axiom audits; no Lean execution."""
from pathlib import Path
import hashlib,json,re,sys,subprocess
E=Path(__file__).resolve().parent;R=E.parents[4];P=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
records=[];failures=[]
for f in sorted(E.glob('*/receipt.json')):
 r=json.loads(f.read_text());r.update(receipt=str(f.relative_to(E)),receipt_sha256=sha(f))
 cmd=E/f.parent.name/'command.json'
 r['command_sha256']=sha(cmd)
 r['deps_fingerprint']=hashlib.sha256(json.dumps(r['imports'],sort_keys=True).encode()).hexdigest()
 assert r['swaps']==0
 if r['exit_status']:
  r['errors']=(f.parent/'lean.log').read_text();failures.append(r);continue
 assert r['peak_rss_bytes'] and r['peak_rss_bytes']<8*1024**3
 src=R/r['source'];assert sha(src)==r['source_sha256']
 assert len(re.findall(r'^#print axioms',src.read_text(),re.M))==len(r['axiom_reports'])
 for line in r['axiom_reports']:
  match=re.search(r'\[([^\]]*)\]',line,re.S)
  axioms={v.strip() for v in match[1].split(',')} if match else set()
  assert axioms<=allowed,line
 r['theorems']=[re.search("'([^']+)'",line)[1] for line in r['axiom_reports']]
 obj=Path('/tmp/codex-cx-ckpt-log-20261020-objects')/(r['module']+'.olean')
 r['object_sha256']=sha(obj);r['object_size']=obj.stat().st_size
 records.append(r)
assert {r['module'] for r in records}=={'RawTx1DigestLog','RawTx1CheckpointBoundary','RawTx1GlobalOracleFull25','RawTx1SamplerSuffixOracle'}
external=json.loads((E/'landed-sampler-pins.json').read_text())
assert external['source_sha256']==external['retained_receipt']['source_sha256']
source_maps={
 'ExtractedTx1Model':'lean/bridge-tx1-e5c186ba3-20261016/ExtractedTx1Model.lean',
 'RawSourceGlobalOracleInitial':'lean/RawSourceGlobalOracleInitial.lean',
 'RawSourceGlobalOracleFull25':'lean/RawSourceGlobalOracleFull25.lean',
}
pins={k:dict(source=str((P/v).relative_to(R)),source_sha256=sha(P/v)) for k,v in source_maps.items()}
manifest=dict(schema='focused-extractor-proof-packet-v1',base_revision=records[0]['source_revision'],modules=records,failed_attempts=failures,direct_import_source_pins=pins,external_landed_dependency='landed-sampler-pins.json',standard_axioms_only=True,no_shared_objects_rewritten=True,scope='R10 conditional tx1 log assembly/full25/suffix bridges; R15 extraction obstruction. Whole-tx1 inventory, source re-pins, checkpoint/account writer, tx2 and cross-transaction consistency remain open. No release manifest replay.')
if '--write' in sys.argv:(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
else:assert json.loads((E/'manifest.json').read_text())==manifest
print(json.dumps(dict(modules=len(records),theorems=sum(len(r['theorems']) for r in records),failed_attempts=len(failures),max_rss_bytes=max(r['peak_rss_bytes'] for r in records))))
