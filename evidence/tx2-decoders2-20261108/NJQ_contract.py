"""Actual frozen decoder contracts against an independent safe reference, (ah)."""
from NJQ_rerun import *
from NJQ_patch import read_patch

def contract(a,name,invert=False,mode="plain",witness_from=None):
 if invert:
  previous=witness_from or a[:-3]+f"{int(a[-3:])-1:03d}"
  assert json.loads((E/previous/'receipt.json').read_text())['exit_status']==0, 'No control after failed positive'
 x,original,files=historical('NIJ_K120')
 module='NJQ_'+name
 parent='crates/aspis-statement/src/pool_v1/format.rs' if name=='identity' else 'crates/aspis-statement/src/pool_v1/verifier_registry.rs'
 key='NIJ_src/'+parent
 text=read_patch(module)
 if witness_from:
  assert invert and name=='registry' and mode.startswith('split_')
  witness=[65,83,82,71,2,4,0,0]+[0]*120
  if mode=='split_bump':
   witness[5]=2;witness[8]=1;witness[72]=1;witness[112]=1
  old='let bytes:[u8;128]=kani::any();'
  assert text.count(old)==1
  text=text.replace(old,'let bytes:[u8;128]=['+','.join(map(str,witness))+'];')
 files[key]+='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
 files['NIJ_src/'+str(Path(parent).parent/(module+'.rs'))]=text
 files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("['NIJ_entry'", "['"+module+"','NIJ_entry'")
 func={'identity':'decode_pool_identity_v1','registry':'decode_verifier_registry_v1','entry':'decode_verifier_registry_entry_v1'}[name]
 length={'identity':144,'registry':128,'entry':192}[name]
 header='pub fn '+func+'('
 check='(*r == '+module+'::decode_ref(bytes))' if name=='identity' else module+'::matches_reference(bytes,r)'
 if mode.startswith('split_'):
  assert name=='registry' or mode=='split_head'
  part=mode.removeprefix('split_');assert part in ['bump','coordinates','flags','zero','authority','delay','head','range']
  check=module+'::check_'+part+'(bytes,r)'

 predicate=check if mode in ['split_coordinates','split_bump'] else check+' != cfg!(NJQ_invert)'
 attr='#[cfg_attr(kani,kani::requires(bytes.len()=='+str(length)+'))]\n#[cfg_attr(kani,kani::ensures(|r| '+predicate+'))]\n#[cfg_attr(kani,kani::modifies())]\n'
 if mode in ['split_flags','split_zero','split_authority','split_delay']:
  attr='#[cfg_attr(kani,kani::requires('+module+'::header_ok(bytes)))]\n'+attr
 assert files[key].count(header)==1;files[key]=files[key].replace(header,attr+header)
 anns=json.loads(files['NGL_CONTRACT_ANNOTATIONS.json']);anns[header]=attr
 if mode in ['validator','composed']:
  child='validate_verifier_registry_v1' if name=='registry' else 'validate_verifier_registry_entry_v1'
  param='registry' if name=='registry' else 'entry'
  child_header='pub fn '+child+'('
  child_attr='#[cfg_attr(kani,kani::ensures(|r| (*r == '+module+'::validate_ref('+param+')) != cfg!(NJQ_child_invert)))]\n#[cfg_attr(kani,kani::modifies())]\n'
  assert files[key].count(child_header)==1;files[key]=files[key].replace(child_header,child_attr+child_header);anns[child_header]=child_attr
 files['NGL_CONTRACT_ANNOTATIONS.json']=json.dumps(anns)
 pins=json.loads(files['NIJ_SOURCE_PINS.json'])
 for n,t in files.items():
  if n.startswith('NIJ_src/') and not n.endswith('Cargo.lock'):pins[n[len('NIJ_src/'):]]=sha(t.encode())
 files['NIJ_SOURCE_PINS.json']=json.dumps(pins)
 manifest='/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107/NIJ_src/crates/aspis-statement/Cargo.toml'
 features=','.join(json.loads((E.parent/'slice-d-entry5-20261107/NIJ_STATEMENT_FEATURES.json').read_text()))
 cmd=x['native_command'];cmd[cmd.index('--manifest-path')+1]=manifest;cmd[cmd.index('--features')+1]=features;cmd[cmd.index('--harness')+1]='pool_v1::'+('format' if name=='identity' else 'verifier_registry')+'::'+module+('::validate_contract' if mode=='validator' else '::decode_contract')
 if mode=='validator':x['env']['RUSTFLAGS']=x['env'].get('RUSTFLAGS','')+' --cfg NJQ_validator_enabled'
 if mode=='composed':x['env']['RUSTFLAGS']=x['env'].get('RUSTFLAGS','')+' --cfg NJQ_composed'
 if invert:x['env']['RUSTFLAGS']=x['env'].get('RUSTFLAGS','')+(' --cfg NJQ_child_invert' if mode=='validator' else ' --cfg NJQ_invert')
 x.update(sources=list(files),module=module+'::decode_contract',root_package='aspis-statement',metadata_manifest=manifest,metadata_features=features,expected_time='optimized compilation then full-Result decoder contract',control=('inverted ensures on fixed valid witness; split from '+witness_from) if witness_from else ('inverted ensures' if invert else 'positive empty-modifies contract'))
 return run(a,'NIJ_K120',(x,original,files))
if __name__=='__main__':contract(sys.argv[1],sys.argv[2],'invert' in sys.argv,sys.argv[3] if len(sys.argv)>3 and sys.argv[3]!='invert' else 'plain',next((v.removeprefix('witness:') for v in sys.argv if v.startswith('witness:')),None))
