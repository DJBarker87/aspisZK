#!/usr/bin/env python3
"""Source-only selected-cut raw release audit; --released hashes private data."""
from pathlib import Path
import hashlib,json,sys,stat
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'sdk-selected-cut-export-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((P/'release.json').read_text());m=json.loads((P/'release-manifest.json').read_text());assert sha(P/'release-manifest.json')==r['manifest_sha256']
a=m['summary'];assert a==dict(baseline_constants=28506,conflicts=0,constants=12,duplicates=0,missing_seeds=[],modules=4,unresolved=[])
assert m['combined_constants']==28518 and m['new_unsafe_or_partial']==[] and m['all_previous_selected_inputs_unchanged']
assert len(m['bases'])==2 and sum(b['constants'] for b in m['bases'])==28506 and sum(b['transport_modules'] for b in m['bases'])==1428
for b,folder in zip(m['bases'],['sdk-current-export-20261024','sdk-current-incremental-20261024']):
 old=json.loads((E/folder/'release.json').read_text());assert b['location']==old['location'] and b['manifest_sha256']==old['manifest_sha256']
for attempt,row in m['ledger'].items():
 d=E/attempt;rec=json.loads((d/'receipt.json').read_text());assert all(rec[k]==v for k,v in row.items()) and rec['exit_status']==0 and rec['swaps']==0 and sha(d/'source.lean')==rec['source_sha256'] and '-j1' in rec['command'] and '-M4400' in rec['command']
for name in ['post-export-inputs.json','post-audit-inputs.json']:
 d=json.loads((P/name).read_text());assert d['all_unchanged'] and all(x['unchanged'] for x in d['files'])
g=json.loads((P/'audit-generator.json').read_text());assert sha(R/g['source'])==g['source_sha256'] and sha(S/'S126SdkSelectedCutAuditV1.lean')==g['output_sha256']
source=(S/'S126SdkSelectedCutAuditV1.lean').read_text();assert 'for c in data.constants do baseNames := baseNames.insert c.name' in source and 'baseNames.contains dep' in source
assert 'baseline.foldl (fun s n => s.insert n.toName)' not in source
bad=json.loads((P/'excluded-audit-v1.json').read_text());assert not bad['accepted'] and bad['compiler_exit_status']==0 and bad['observed_baseline_constants']==28459 and bad['expected_baseline_constants']==28506
assert sha(E/'sdk-selected-cut-audit-v1/source.lean')==bad['source_sha256'] and sha(E/'sdk-selected-cut-audit-v1/lean.log')==bad['log_sha256']
for rel,h in json.loads((P/'tool-pins.json').read_text()).items():assert sha(R/rel)==h
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.a','.o','.pyc'] for p in P.rglob('*') if p.is_file()) and not any(p.stat().st_size>5_000_000 for p in P.glob('*.json'))
if '--released' in sys.argv:
 d=Path(r['location']);assert sha(d/'manifest.json')==r['manifest_sha256']
 for f in m['files']:
  p=d/f['relative'];assert not p.is_symlink() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'] and stat.S_IMODE(p.stat().st_mode)&0o222==0
 assert stat.S_IMODE(d.stat().st_mode)&0o222==0
 for b in m['bases']:
  d=Path(b['location']);assert sha(d/'manifest.json')==b['manifest_sha256'] and sha(d/b['constant_file'])==b['constant_file_sha256']
print(json.dumps(dict(status='PASS',new_fragments=4,new_constants=12,base_fragments_reused=1428,combined_constants=28518,exact_Name_values=True,released_payload_hashed='--released' in sys.argv,scope=m['scope'])))
