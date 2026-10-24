#!/usr/bin/env python3
"""Check the concrete P3 program instance, retaining native runtime residuals."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
m=load(E/'s1-prepared-oracle-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-prepared-oracle-import-pins.json');wall=0.;rss=0;reports=0
for target,attempt in m['targets'].items():
 p=S/(target+'.lean');r=load(E/attempt/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
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
for rel,row in load(E/'s1-prepared-oracle-reused-sources.json')['sources'].items():assert sha(S/'reused-p3-sources'/rel)==row['sha256']
for rel,h in load(E/'s1-prepared-oracle-producer-evidence-pins.json')['files'].items():assert sha(E/rel)==h
for path,h in load(E/'s1-prepared-oracle-tool-pins.json')['scripts'].items():assert sha(R/path)==h
for rel,h in load(E/'s1-prepared-oracle-reused-pins.json')['packets'].items():assert sha(E/rel)==h
s=(S/'S1ClosedPreparationOracleV1.lean').read_text()
assert 'closedPreparation_oracle_exact' in s and 'closedPreparation_oracle_installed' in s
assert 'p3_public_record_eq_model' in s and 'publicToCurrent (p3PublicDigest32 sha)' in s
assert '(valid :' not in s and '(law :' not in s
retarget=load(E/'s1-prepared-oracle-wrapper-retarget.json')
old=(S/'reused-p3-sources/S4SolanaDigestWrapperP3BindingV1.lean').read_text()
new=(S/'S1ReusedSolanaDigestWrapperP3V1.lean').read_text()
assert new==old.replace('import AspisR1CurrentCaller.Types','import CurrentCompactCallerTypesV1')
assert sha(S/'S1ReusedSolanaDigestWrapperP3V1.lean')==retarget['target_sha256']
assert all(row['matches_existing_packet'] for row in load(E/'s1-prepared-oracle-native-wrapper-source-pins.json')['revisions'].values())
parent=(S/'S1OwnedStage1PreparationOracleV1.lean').read_text()
assert 'owned_stage1_preparation_oracle' in parent and 'first_current_prepared_new' in parent
assert '(valid :' not in parent and '(hfirst :' not in parent and '(hnew :' not in parent
causal=(S/'S1ClosedPreparationCausalProgramV1.lean').read_text()
assert '(claimLaw :' not in causal and '(valid :' not in causal
assert 'owned_stage1_causal_preparation_oracle' in causal and 'closedPreparation_dictionary_irrelevant' in causal
fixed=causal[causal.index('def causalPreparationProgram'):causal.index('theorem causalPreparation_exact')]
assert '(sha :' not in fixed
assert m['oracle_dictionary_independence'] and m['owned_caller_connection']
assert m['concrete_p3_validity_derived'] and m['complete_ordered_reads']
assert not m['native_runtime_binding'] and not m['frozen2_prepare_join'] and not m['whole_s1_closed']
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,standard_or_empty_axiom_reports=reports,concrete_p3_validity_derived=True,native_runtime_binding=False,whole_s1_closed=False)))
