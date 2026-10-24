#!/usr/bin/env python3
"""Audit accepted source scanner/caller evidence; native residuals stay explicit."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(Path(__file__).with_name('scan-driver-generate.py')),'--check'],check=True)
m=load(E/'s1-query-scanner-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-query-scanner-import-pins.json');wall=0.;rss=0;reports=0
for target,attempt in m['targets'].items():
 p=S/(target+'.lean');r=load(E/attempt/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms'],target
 assert a[target]['receipt']==attempt+'/receipt.json'
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert r['object_sha256']==pins['targets'][target]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide|bv_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for x in r['print_axioms']:
  ax=re.search(r'depends on axioms:\s*\[([^]]*)\]',x,re.S)
  assert ax and set(re.findall(r'[A-Za-z_.]+',ax[1]))<={'propext','Classical.choice','Quot.sound'},(target,x)
  reports+=1
 wall+=r['wall_seconds'];rss=max(rss,r['peak_rss_bytes'])
 for f in (E/attempt).rglob('*'):
  if f.is_file():assert f.suffix not in ['.olean','.llbc','.rlib','.rmeta','.o','.a','.so','.dylib']
for kind,key in [('tool','scripts'),('source','sources'),('reused','packets')]:
 for path,h in load(E/f's1-query-scanner-{kind}-pins.json')[key].items():assert sha(R/path)==h,path
word=(S/'S1QueryWordModelV1.lean').read_text();assert 'out.val.map (fun w => w.val)' in word and 'query_words_math' in word
step=(S/'S1QueryScanModelStepV1.lean').read_text();assert 's.draws+xs.length' in step and 'draws : s.draws.val<64' in step
driver=(S/'S1QueryScanDriverModelV1.lean').read_text();assert 'cases trace with' in driver and 'lastStop' in driver
for k in range(8):assert f'| stop{k} ' in driver
meaning=(S/'S1RankTraceQueryScannerV1.lean').read_text();assert 'materializedOutputs pairs blocks advances' in meaning and 'R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0' in meaning
parent=(S/'S1CurrentOwnedScannerJoinV1.lean').read_text();assert 'current_owned_stage1_closed_claim_and_rank adapterOps ops' in parent and 'exactRankTrace_query_scanner' in parent
assert '(hquery :' not in parent and '(scanner :' not in parent and '(hfirst :' not in parent
assert m['same_owned_parent'] and m['accepted_scanner_value_and_selected_state_equal']
assert not m['native_iterator_binding'] and not m['native_sdk_binding'] and not m['whole_s1_closed'] and not m['whole_s6_closed']
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,standard_axiom_reports=reports,accepted_scanner_value_and_selected_state_equal=True,same_owned_parent=True,whole_s1_closed=False)))
