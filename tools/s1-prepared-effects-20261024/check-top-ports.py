#!/usr/bin/env python3
"""Audit the full-carrier preparation and top powers candidate packet."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(E/'s1-top-ports-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-top-ports-import-pins.json');wall=0.;rss=0;reports=0
for target,attempt in m['targets'].items():
 p=S/(target+'.lean');r=load(E/attempt/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms'],target
 assert a[target]['receipt']==attempt+'/receipt.json'
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert r['object_sha256']==pins['targets'][target]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide|bv_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for x in r['print_axioms']:
  if 'does not depend on any axioms' not in x:
   ax=re.search(r'depends on axioms:\s*\[([^]]*)\]',x,re.S)
   assert ax and set(re.findall(r'[A-Za-z_.]+',ax[1]))<={'propext','Classical.choice','Quot.sound'},(target,x)
  reports+=1
 wall+=r['wall_seconds'];rss=max(rss,r['peak_rss_bytes'])
 for f in (E/attempt).rglob('*'):
  if f.is_file():assert f.suffix not in ['.olean','.llbc','.rlib','.rmeta','.o','.a','.so','.dylib']
for path,h in load(E/'s1-top-ports-source-pins.json')['sources'].items():assert sha(R/path)==h,path
for path,h in load(E/'s1-top-ports-tool-pins.json')['scripts'].items():assert sha(R/path)==h,path
for name,row in load(E/'s1-top-prepare-reused-source-pins.json')['modules'].items():
 assert sha(R/row['snapshot'])==row['source_sha256'],name
source=(S/'S1TopPrepareSourceV1.lean').read_text()
assert 'closedInstall ops' in source and 'prepare_return ops D pub proof hash input scratch prepared success' in source
assert 'prepared=toPrepared current ∧ scratch=mapArray toE g' in source
assert 'currentObserver obs' in source
provenance=(S/'S1ClosedPrepareProvenanceV1.lean').read_text()
assert 'PrepareReachability.prepare_success' in provenance and 'originalNew_static' in provenance
assert 'prepared.roots=sem.roots' in provenance and 'prepared.semantic_alpha=sem.alpha' in provenance
powers=(S/'S1TopPowersV1.lean').read_text()
assert 'ClaimPowers.powers_total_exact N (claimE x) canonical' in powers
assert 'cases Result.ok.inj success' in powers
assert m['full_prepared_carrier'] and m['same_prepare_return_and_scratch']
assert m['top_powers_total_for_canonical_input']
writer=(S/'S1TopWriterVariantV1.lean').read_text()
assert 'Port4A_PrepareCut.variant_of_prepare' in writer and 'prepare_variant sourceOps D semantic proof hash' in writer
assert '(prepareVariant :' not in writer
assert m['enclosing_writer_variant_law_discharged_for_source_body_installation']
for gate in ['native_prepare_binding','full_prepared_binding','whole_s1_closed','whole_s6_closed']:assert not m[gate]
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,standard_or_empty_axiom_reports=reports,whole_s1_closed=False,whole_s6_closed=False)))
