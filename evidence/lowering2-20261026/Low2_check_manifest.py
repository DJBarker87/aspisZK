#!/usr/bin/env python3
"""Verify L186's source pins, exact recorded bridge, compiled inputs and S10 cuts.
No compilation is launched. This verifies retained compiler evidence under P7;
it does not prove compiler semantics or any other source/runtime ledger row.
"""
from pathlib import Path
import collections,hashlib,importlib.util,json,resource,subprocess,sys,time
R=Path(__file__).resolve().parents[2]; E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda n:json.loads((E/n).read_text())
PINS={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}

def main():
 start=time.monotonic();s=load('Low2_source_pin_check.json');inputs=load('Low2_build_inputs.json');b=load('Low2_build_manifest.json');g=load('Low2_elf_graphs.json')
 assert not s['errors'];assert s['source_revision']==inputs['source_revision']==b['source_revision']
 for p,h in inputs['files'].items():assert sha(R/p)==h,p
 for r in s['evidence_files']:assert sha(R/r['path'])==r['sha256'],r
 assert len(s['packet_roots'])==15
 spec=importlib.util.spec_from_file_location('Low2_source_checker',E/'Low2_check_source_pins.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 assert mod.bridge()==s['bridge']
 source_receipt=load('Low2_source_pin_receipt.json')
 assert source_receipt['exit_status']==0 and source_receipt['checker_sha256']==sha(E/'Low2_check_source_pins.py')
 for r in s['verification_source_pins']:
  assert r['retained_exact_files']
  assert all(sha(R/p)==r['expected_sha256'] for p in r['retained_exact_files'])
 compiled=collections.defaultdict(set);generated=[]
 assert {r['mode'] for r in b['builds']}==set(PINS)
 for r in b['source_checks']:assert r['expected_sha256']==r['actual_sha256']==inputs['files'][r['path']]
 rustc=set()
 for build in b['builds']:
  mode=build['mode'];rec=build['receipt'];art=build['artifact'];actual=g['artifacts'][mode]
  assert rec['exit_status']==0 and rec['swaps']==0 and rec['actual_build_source_revision']==inputs['source_revision']
  assert rec['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert art['sha256']==art['expected_sha256']==PINS[mode] and art['byte_identical']
  assert actual['deployed']['sha256']==PINS[mode] and actual['deployed']['bytes']==art['bytes'] and actual['text_equal']
  assert '3.1.13' in build['command']['command'][0] and '--locked' in build['command']['command']
  features=build['command']['command'][build['command']['command'].index('--features')+1]
  assert features==('r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts')
  for inv in build['compiler_invocations']:
   rustc.add(inv['rustc_sha256']);assert 'rustc 1.89.0-dev' in inv['rustc_version']
   assert 'opt-level=3' in ' '.join(inv['args']) or 'opt-level=2' in ' '.join(inv['args'])
  assert build['compiler_invocations']
  for row in build['repository_compiler_inputs']:
   assert row['sha256']==inputs['files'][row['path']]==sha(R/row['path'])
   compiled[row['path']].add(mode)
  generated+=build['generated_compiler_inputs']
 assert len(rustc)==1
 # Validate that the S10 algorithms are unchanged except literal private paths
 # and the failed default-v1 / successful default-v2 build-directory coordinate.
 relocations={}
 old='/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023';new='/home/dombarker/project-offloads/codex-cx-lowering2-20261026'
 for name in ('collect-host','ordering-host','cfg-host'):
  original=R/('tools/s10-repin3-20261023/'+name+'.py');copy=E/('Low2_'+name.replace('-','_')+'.py')
  expected=original.read_text().replace(old,new).replace("'build-default-v1'","'build-default-v2'")
  if name=='collect-host':expected=expected.replace("d=H/('build-'+mode+'-v1')", "d=H/('build-'+mode+('-v2' if mode=='default' else '-v1'))")
  assert copy.read_text()==expected
  receipt=load('Low2_'+name.replace('-','_')+'-v2_receipt.json');assert receipt['exit_status']==0 and receipt['swaps']==0
  relocations[name]={'original':str(original.relative_to(R)),'original_sha256':sha(original),'relocated_sha256':sha(copy),'algorithm_unchanged':True}
 original=R/'tools/s10-repin3-20261023/ordering-map.py'
 expected=original.read_text().replace("E=B/'s10-repin3-20261023'", "E=R/'evidence/lowering2-20261026'")
 expected=expected.replace("E/'ordering-observations.json'", "E/'Low2_ordering_observations.json'").replace("E/'cfg.json'", "E/'Low2_cfg.json'").replace("E/'ordering-repin-map.json'", "E/'Low2_ordering_repin_map.json'")
 assert (E/'Low2_ordering_map.py').read_text()==expected
 relocations['ordering-map']={'original':str(original.relative_to(R)),'original_sha256':sha(original),'relocated_sha256':sha(E/'Low2_ordering_map.py'),'algorithm_unchanged':True}
 check=subprocess.run(['python3','-B',str(E/'Low2_ordering_map.py'),'--check'],cwd=R,capture_output=True,text=True)
 assert check.returncode==0,check.stderr
 order=load('Low2_ordering_repin_map.json');cfg=load('Low2_cfg.json')
 assert order['all_140_preserved'] and not order['reselected_facts']
 assert len(order['facts'])==sum(len(f['cuts']) for f in cfg['functions'])==140
 assert order['changed_bodies']==0 and order['coordinate_changes']==0
 links=[]
 for path in sorted({r['source'] for r in s['checks']}):
  pins=sorted({r['expected_sha256'] for r in s['checks'] if r['source']==path})
  for r in (r for r in s['checks'] if r['source']==path):
   assert r['status'] in ('match','bridged')
   assert r['release_sha256']==r['build_input_sha256']==inputs['files'][path]
   assert r['expected_sha256']==inputs['files'][path] or (r['status']=='bridged' and path==s['bridge']['source'] and r['expected_sha256']==s['bridge']['old_sha256'])
  category='compiled_rust_input' if path in compiled else ('cargo_configuration' if path.endswith(('Cargo.lock','Cargo.toml')) else 'inventory_file_not_compiled_in_release_features')
  links.append({'source':path,'certificate_pins':pins,'release_sha256':inputs['files'][path],'compiled_modes':sorted(compiled[path]),'classification':category,'bridge':s['bridge']['delta'] if len(pins)>1 else None})
 assert all(path in {r['source'] for r in links} for path in compiled if compiled[path])
 out={'row':'L186','status':'evidence_gates_pass_under_retained_P7','source_revision':inputs['source_revision'],'audit_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'trust_retained':['P7 rustc/LLVM/SBF toolchain','existing D188 extraction association','existing P6/Kani association','existing S4 source-equivalence translation boundary'],'new_trust_items':[],'source_links':links,'classifications':dict(collections.Counter(r['classification'] for r in links)),'source_pin_counts':s['counts'],'verification_kit_pins':len(s['verification_source_pins']),'generated_compiler_inputs':generated,'artifacts':{r['mode']:r['artifact'] for r in b['builds']},'s10':{'facts':140,'all_preserved':True,'changed_mir_bodies':0,'algorithm_relocations':relocations,'map_check_stdout':check.stdout},'budget_used':{'sbf':4,'kani':0,'lean':0},'qualification':'All whole release-source pins match or use the mechanically verified recorded S4 delta. The manifest distinguishes actual compiler inputs from inventories of tests/examples/feature-disabled modules and verification-only kit files; those are never asserted to be compiled. P7 connects extraction sources to the pinned code; no Lean compiler-correctness, other execution identity, or headline security conclusion is asserted.'}
 (E/'Low2_source_to_elf_manifest.json').write_text(json.dumps(out,indent=2)+'\n')
 usage=resource.getrusage(resource.RUSAGE_SELF)
 receipt={'target':'L186 final source/certificate/ELF/order manifest','command':['python3','-B','evidence/lowering2-20261026/Low2_check_manifest.py'],'source_revision':inputs['source_revision'],'exit_status':0,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,'swaps':usage.ru_nswap,'checker_sha256':sha(Path(__file__)),'manifest_sha256':sha(E/'Low2_source_to_elf_manifest.json'),'deps_fingerprint':hashlib.sha256(''.join(sha(E/p) for p in ['Low2_build_inputs.json','Low2_build_manifest.json','Low2_source_pin_check.json','Low2_elf_graphs.json','Low2_cfg.json','Low2_ordering_repin_map.json']).encode()).hexdigest(),'print_axioms':'No new theorem or Lean invocation. Exact accepted S4 standard-axioms audit reused and mechanically verified.'}
 (E/'Low2_final_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'row':'L186','status':out['status'],'classifications':out['classifications'],'source_pin_counts':s['counts'],'ordering_facts':140,'budget_used':out['budget_used']}))
if __name__=='__main__':main()
