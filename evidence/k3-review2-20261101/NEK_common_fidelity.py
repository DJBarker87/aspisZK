"""Required same-interface Box/common contract fidelity controls, no global log."""
from NEK_common_batch import *

def make_fidelity():
 base=read_json(E/'NEK_COMMON_IMMUTABLE_v2.json.xz');p='programs/r1-cost-probe/src/r1_pool_adapter.rs';m='programs/r1-cost-probe/src/NDM_native.rs'
 base[m]=base[m].replace('pub(super) level:usize}', 'pub(super) level:usize,pub(super) frame:core::cell::Cell<u8>}').replace('NEK_Context{index:k,level:l}', 'NEK_Context{index:k,level:l,frame:core::cell::Cell::new(kani::any())}')
 base[p]=base[p].replace('NEK_Context{index:0,level:0}', 'NEK_Context{index:0,level:0,frame:core::cell::Cell::new(0)}')
 weak='#[cfg_attr(all(kani,feature="NEK_shape_weak"),kani::ensures(|r| (r.output_lane==authenticated.selected_lane.lane_id) != cfg!(feature="NEK_invert")))]\n#[cfg_attr(kani,kani::modifies())]\n'
 base[p]=base[p].replace('fn asq8_common(',weak+'fn asq8_common(',1)
 at=base[p].index('fn asq8_common(');brace=base[p].index('{',at);i=brace+1;depth=1
 while depth:
  if base[p][i]=='{':depth+=1
  elif base[p][i]=='}':depth-=1
  i+=1
 bad=base[p][at:i].replace('fn asq8_common(', 'fn NEK_bad_modifies(',1).replace('{','{record.frame.set(record.frame.get().wrapping_add(1));',1)
 bad='#[cfg(kani)]\n#[kani::requires(record.index<32 && record.level<aspis_statement::pool_v1::POOL_V1_PAIR_TREE_DEPTH)]\n#[kani::modifies()]\n#[kani::ensures(|r| r.output_lane==authenticated.selected_lane.lane_id)]\n'+bad
 base[p]+='\n'+bad+'\n'
 n=base[m];at=n.index('fn common_contract(){');brace=n.index('{',at);i=brace+1;depth=1
 while depth:
  if n[i]=='{':depth+=1
  elif n[i]=='}':depth-=1
  i+=1
 body=n[brace+1:i-1]
 attrs='#[kani::unwind(34)]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEK_kmx::KMX_copy_nonoverlapping)]\n'
 for name,stub in [('NEK_real',False),('NEK_unimplied',True)]:
  b=body.replace('let _=asq8_common(&record,&a,&c);','let r=asq8_common(&record,&a,&c);assert!(r.checkpoint_sequence==a.checkpoint.checkpoint_sequence,"NEK_unimplied_checkpoint");')
  base[m]+='\n#[kani::proof]\n'+('#[kani::stub_verified(super::asq8_common)]\n' if stub else '')+attrs+'fn '+name+'(){'+b+'}\n'
 b=body.replace('let _=asq8_common(&record,&a,&c);','let _=super::NEK_bad_modifies(&record,&a,&c);')
 base[m]+='\n#[kani::proof_for_contract(super::NEK_bad_modifies)]\n'+attrs+'fn NEK_modifies(){'+b+'}\n'
 manifest='programs/r1-cost-probe/Cargo.toml';base[manifest]=base[manifest].replace('[features]','[features]\nNEK_shape_weak = []',1)
 (E/'NEK_COMMON_FIDELITY.json.xz').write_bytes(lzma.compress(json.dumps(base,sort_keys=True).encode()))
 return base

def run(start=190):
 base=make_fidelity();upload(base)
 # Same parameter and result types throughout, including the harness-local Cell
 # which supplies a safe-Rust modifies violation without a written static.
 tests=[('common_contract',False),('common_contract',True),('NEK_real',False),('NEK_unimplied',True),('NEK_modifies',True)]
 for j,(name,negative) in enumerate(tests):
  a=f'NEK_K{start+j:03}'
  if (E/a/'receipt.json').exists():continue
  item=dict(attempt=a,original_receipt='evidence/native-front4b-20261028/NDM_K035/receipt.json',cfg='NEK_shape_weak',clause='fidelity',negative=negative)
  x=cfg(item,base)
  # Negation applies only to the inverted-ensures check, not the two other
  # deliberately failing controls (which need the real weak postcondition).
  if name!='common_contract':
   k=x['native_command'].index('--features')+1;x['native_command'][k]=x['native_command'][k].replace(',NEK_invert','')
  x['native_command'][x['native_command'].index('--harness')+1]='r1_pool_adapter::NDM_native::'+name;x['module']='r1_pool_adapter::NDM_native::'+name
  x['deps_fingerprint'].update(support_role='Box_common_shape_fidelity',fidelity_bundle_sha256=sha((E/'NEK_COMMON_FIDELITY.json.xz').read_bytes()))
  rc=launch(x)
  r=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{p.name:p.read_text() for p in b.glob({(a+'-*check.json')!r})}}))
''');assert r.returncode==0
  for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
  v=verdict((E/a/'stdout.log').read_text());row=dict(attempt=a,original_receipt=item['original_receipt'],verdict=v,expected='FAIL' if negative else 'PASS',negative=negative,method='same Box/common interface shape fidelity',support_role='Box_common_shape_fidelity',case=name)
  with (E/'NEK_RESULTS.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  if 'error: could not compile' in (E/a/'stdout.log').read_text():raise SystemExit('own fidelity compile error; inspect before further calls')
if __name__=='__main__':
 if os.environ.get('NEK_PLAN_ONLY'):print(len(make_fidelity()),'source files; Box shape controls prepared')
 else:run(int(sys.argv[1]) if len(sys.argv)>1 else 190)
