#!/usr/bin/env python3
"""Audit source-code/mathematical materialization joins; retain native residuals."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['materialize-generate.py','materialize-pairs-generate.py','materialize-program-generate.py']:
 subprocess.run([sys.executable,str(Path(__file__).with_name(name)),'--check'],check=True)
m=load(E/'s1-query-materializer-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-query-materializer-import-pins.json');wall=0.;rss=0;reports=0
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
for path,h in load(E/'s1-query-materializer-tool-pins.json')['scripts'].items():assert sha(R/path)==h
for name,h in load(E/'s1-query-materializer-reused-pins.json')['packets'].items():assert sha(E/name)==h
for path,h in load(E/'s1-query-materializer-source-pins.json')['sources'].items():assert sha(R/path)==h
model=(S/'S1QueryMaterializeModelV1.lean').read_text()
assert 'AspisR1.QuerySampler.chain p packEight 8' in model and '| _,_ => .fail .panic' in model
assert 'materialize_eq_model' in model and '(success :' not in model and '(bound :' not in model
prefix=(S/'S1QueryMaterializeProgramV1.lean').read_text();assert prefix.count('  .ask ')==16
row=(S/'S1QueryRow31ProgramV1.lean').read_text();assert 'query31_reads' in row and '.1.length=17' in row
parent=(S/'S1OwnedStage1QueryPairsV1.lean').read_text()
assert 'owned_stage1_query_pairs_oracle' in parent and 'v.variant=.S2' in parent
assert '(hfirst :' not in parent and '(hnew :' not in parent and '(variant :' not in parent
assert m['full_code_equal'] and m['fixed_math_materializer_equal'] and m['source_model_materializer_total']
assert m['explicit_query31_reads']==17 and not m['query_decoder_math_equivalence'] and not m['native_sdk_binding'] and not m['whole_s1_closed']
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,standard_or_empty_axiom_reports=reports,fixed_math_materializer_equal=True,source_model_materializer_total=True,query31_reads=17,whole_s1_closed=False)))
