#!/usr/bin/env python3
"""Assemble/verify a focused proof packet without executing Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path(__file__).resolve().parent;ROOT=E.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
records=[];failures=[]
for p in sorted(E.glob('*/receipt.json')):
 r=json.loads(p.read_text());r.update(receipt=str(p.relative_to(E)),receipt_sha256=sha(p),process_swap_count=r['swaps'],swap_bytes=None)
 if r['exit_status']:
  failures.append(r);continue
 if r['module']=='CodecImportAudit':continue
 assert r['peak_rss_bytes'] is not None and r['swaps']==0
 for line in r['axiom_reports']:
  m=re.search(r'\[([^\]]*)\]',line,re.S)
  assert m and {a.strip() for a in m[1].split(',')}<=allowed,line
 src=ROOT/r['source'];assert sha(src)==r['source_sha256']
 assert len(re.findall(r'^#print axioms',src.read_text(),re.M))==len(r['axiom_reports'])
 r['theorems']=[re.search("'([^']+)'",line)[1] for line in r['axiom_reports']]
 records.append(r)
mods={r['module'] for r in records}
assert {'ExtractedAdapterTransferBindings','ExtractedAdapterStageBindingObligations'}<=mods,mods
source_map={}
for r in records:
 for x in r['imports']:
  n=x['module']
  candidates=list((ROOT/'docs/research/100bit-spend-path-20261013/lean').glob(n+'.lean'))
  if n=='R1SemanticPublicWireRoundTrip':candidates=[ROOT/'docs/research/100bit-spend-path-20261013/lean/SemanticPublicWireRoundTrip.lean']
  if candidates:source_map[n]=dict(source=str(candidates[0].relative_to(ROOT)),sha256=sha(candidates[0]),import_object_sha256=x['sha256'])
manifest=dict(schema='focused-extractor-proof-packet-v1',publication_base_revision=records[0]['source_revision'],modules=records,failed_attempts=failures,direct_import_source_map=source_map,scope='R8 retained adapter transfer success and payload bindings; conditional named R9 obligations only. Focused local checks; no full frozen manifest replay.',no_shared_objects_rewritten=True,standard_axioms_only=True)
if '--write' in sys.argv:(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
else:
 assert json.loads((E/'manifest.json').read_text())==manifest
print(json.dumps(dict(verified_modules=len(records),failed_attempts=len(failures),axiom_reports=sum(len(r['axiom_reports']) for r in records))))
