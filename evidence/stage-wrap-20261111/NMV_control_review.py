from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
idx=json.loads((E/'NMV_INPUTS.json').read_text())
def artifact(a,n):
 h=idx['attempts'][a][n];v=lzma.decompress((E/idx['objects'][h]['path']).read_bytes());assert sha(v)==h;return v
pairs=[]
for row,positive,negative,count in [('TX2:240','NMV_K035','NMV_K063',7),('TX1:344','NMV_K041','NMV_K064',3)]:
 p=json.loads((E/(positive+'.json')).read_text());n=json.loads((E/(negative+'.json')).read_text())
 ignored={'LEAN_PATH'}
 assert {k:v for k,v in p['env'].items() if k not in ignored}=={k:v for k,v in n['env'].items() if k not in ignored}
 assert n['env']['LEAN_PATH']==p['env']['LEAN_PATH'] or n['env']['LEAN_PATH'].endswith(':'+p['env']['LEAN_PATH'])
 pc=json.loads(artifact(positive,'NMV_fission_config.json'))['native_command']
 nc=json.loads(artifact(negative,'NMV_fission_config.json'))['native_command']
 hi=pc.index('--harness')+1;assert pc[:hi]+pc[hi+1:]==nc[:hi]+nc[hi+1:]
 source='NMV_src/programs/r1-cost-probe/src/NMV_Fission.rs'
 assert artifact(positive,source)==artifact(negative,source)==(E/'NMV_Fission.rs').read_bytes()
 harness='NMV_src/programs/r1-cost-probe/src/NMV_FissionHarness.rs'
 assert artifact(negative,harness)==artifact(positive,harness)+b'\n'+(E/'NMV_ParentMutantHarness.rs.pending').read_bytes(), 'Exact base harness mismatch'
 for name in ['NMV_program.rs','NMV_parent.rs','r1_pool_adapter_owned.rs','lib.rs']:
  path='NMV_src/programs/r1-cost-probe/src/'+name
  assert artifact(positive,path)==artifact(negative,path),name
 pg=json.loads((E/(positive+'-graph-check.json')).read_text());ng=json.loads((E/(negative+'-graph-check.json')).read_text())
 assert pg['all_crate_features']==ng['all_crate_features']
 assert pg['graph_matches_frozen'] and ng['graph_matches_frozen']
 for a in [positive,negative]:
  assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
  assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
 log=lzma.decompress((E/negative/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- FAILED' in log and f'Failed Checks: assertion failed: l.count == {count}' in log
 assert 'unwinding assertion' not in log
 pairs.append(dict(row=row,positive_reused=positive,negative=negative,negative_assertion=f'l.count == {count}',fission_sha256=sha(artifact(negative,source)),same_frozen_and_fission_sources=True,exact_archived_positive_harness_prefix=True,same_kani_command_and_rust_environment=True,lean_only_path_extension="NNC seed prepended after original passes; not consumed by cargo-kani",same_all_crate_features=True,lock_unchanged=True,receiver='unmodified Log<0>',mutation='parent child call argument &owned -> &owned[1..]',credit='required parent argument control; no unchanged passing rerun'))
mutant=(E/'NMV_ParentMutants.rs.pending').read_text()
base=(E/'NMV_Fission.rs').read_text()
start1=base.index('pub fn stage1');start2=base.index('pub fn stage2')
body=base[start1:].strip()+'\n'+base[start2:start1].strip()+'\n'
expect='use super::super::NMV_Fission::*;\n'+body.replace('&owned, data','&owned[1..], data')
assert mutant==expect
out=dict(status='REQUIRED_PARENT_ARGUMENT_CONTROLS_FAIL',pairs=pairs,mutant_sha256=sha(mutant.encode()),kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',excluded_receiver_controls=['NMV_K037','NMV_K043','NMV_K049','NMV_K053'],new_kani_used=4,supplementary_controls={'NMV_K061':'FAIL later descriptor receiver; superseded for exact K035 match','NMV_K062':'FAIL later descriptor receiver; superseded for exact K041 match'})
(E/'NMV_CONTROL_RESUME.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
