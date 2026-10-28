from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;O=Path('evidence/native-tx2j-20261028')
pos=json.loads((O/'NBU_K050/receipt.json').read_text());neg=json.loads((E/'NBX_K050/receipt.json').read_text())
assert pos['exit_status']==0 and neg['exit_status']!=0
assert all(neg['source_hashes'].get(n)==h for n,h in pos['source_hashes'].items()),'STOP common source mismatch'
assert pos['limits']==neg['limits']
assert all(pos['env'][n]==neg['env'][n] for n in pos['env'] if n not in ['CARGO_TARGET_DIR','TMPDIR'])
assert pos['command'][pos['command'].index('--harness-timeout')+1]==neg['command'][neg['command'].index('--harness-timeout')+1]=='90s'
g=json.loads((E/'NBX_K050-graph.json').read_text());assert g['graph_matches_frozen'] and g['lock_unchanged']
s=(O/'NBU_more.rs.txt').read_text()
def block(n):
 i=s.index('fn '+n+'(');start=s.index('{',i);j=start+1;depth=1
 while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[start:j],s[s.rfind('#[kani::proof]',0,i):i]
a,aa=block('NBU_result_control');b,bb=block('NBU_result_control_negative')
assert aa==bb
assert a.replace('assert_eq!(stage.get(),0)','assert_ne!(stage.get(),0)')==b
out=(E/'NBX_K050/stdout.log').read_text()
pos_out=(O/'NBU_K050/stdout.log').read_text()
pc=re.search(r'\*\* 0 of (\d+) failed',pos_out);nc=re.search(r'\*\* 1 of (\d+) failed',out)
assert pc and nc and pc.group(1)==nc.group(1),('STOP positive/negative property counts differ',out[-2000:])
assert 'core::panicking::assert_failed_inner' in out
assert 'unwinding assertion' not in out.lower()
x=dict(positive='evidence/native-tx2j-20261028/NBU_K050',negative='evidence/native-tx2k-20261028/NBX_K050',common_sources_identical=pos['source_hashes'],limits_identical=True,semantic_env_identical=True,only_env_differences=['CARGO_TARGET_DIR','TMPDIR'],attributes_identical=aa,only_control_change='first reached lane callback: assert_eq!(stage.get(),0) -> assert_ne!(stage.get(),0)',failure_diagnostic=out[out.index('VERIFICATION RESULT:'):],interpretation='expected negative assertion panic path; Kani emits its runtime-format placeholder at assert_failed_inner; unsupported caller_location/foreign-function warnings retained, not hidden; no unwinding/codegen failure',KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',graph=g)
(E/'NBX_CONTROL_PAIR.json').write_text(json.dumps(x,indent=2)+'\n');print('matched original positive, exact one-assertion negative,1/'+nc.group(1)+' failure')
