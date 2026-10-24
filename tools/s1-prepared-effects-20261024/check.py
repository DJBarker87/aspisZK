#!/usr/bin/env python3
"""Audit source-shaped preparation reification; no native oracle join claimed."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021'
S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['generate.py','hash-generate.py','scalar-generate.py','query-generate.py']:
 subprocess.run([sys.executable,str(Path(__file__).with_name(name)),'--check'],check=True)
m=load(E/'s1-prepared-effects-targets.json')
a=load(E/'accepted-targets.json')['targets']
pins=load(E/'s1-prepared-effects-import-pins.json')
wall=0.;rss=0;reports=0
for target,attempt in m['targets'].items():
 p=S/(target+'.lean');r=load(E/attempt/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms'],target
 assert a[target]['receipt']==attempt+'/receipt.json'
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert r['object_sha256']==pins['targets'][target]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for x in r['print_axioms']:
  if 'does not depend on any axioms' not in x:
   ax=re.search(r'depends on axioms:\s*\[([^]]*)\]',x,re.S)
   assert ax and set(re.findall(r'[A-Za-z_.]+',ax[1]))<={'propext','Classical.choice','Quot.sound'},(target,x)
  reports+=1
 wall+=r['wall_seconds'];rss=max(rss,r['peak_rss_bytes'])
 for f in (E/attempt).rglob('*'):
  if f.is_file():assert f.suffix not in ['.olean','.llbc','.rlib','.rmeta','.o','.a','.so','.dylib']
for path,h in load(E/'s1-prepared-effects-tool-pins.json')['scripts'].items():assert sha(R/path)==h
for name,h in load(E/'s1-prepared-effects-reused-pins.json')['packets'].items():assert sha(E/name)==h
assert m['full_result_and_scratch'] and m['queries_materialized_hash_calls']==16
assert not m['native_oracle_binding'] and not m['whole_s1_closed'] and not m['whole_s6_closed']
q=(S/'S1PreparedQueryEffectsV1.lean').read_text()
assert q.count('effects.digest aspis_coreDigest32Inst')==16
c=(S/'S1ClosedPreparationHashCodeV1.lean').read_text()
assert '(B :' not in c[c.index('def closedPreparationCode'):]
assert 'closedHashBoundaries' in c and 'closedHashQueries' in c and 'originalNew_eq_transport' in c
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,
 standard_or_empty_axiom_reports=reports,native_oracle_binding=False,whole_s1_closed=False)))
