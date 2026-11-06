from NJI_rerun import *
def contract(a,name,invert=False):
 x,original,files=historical('NIJ_K120')
 files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("['NIJ_entry'","['NJI_v1','NJI_policy','NJI_accounts','NJI_decoder','NIJ_entry'")
 key='NIJ_src/crates/aspis-statement/src/pool_v1/verifier_registry.rs'
 text=(E/'NJI_v1.rs').read_text()
 files[key]+='\n#[cfg(kani)]\n#[path="NJI_v1.rs"]\nmod NJI_v1;\n'
 files['NIJ_src/crates/aspis-statement/src/pool_v1/NJI_v1.rs']=text
 anns=json.loads(files['NGL_CONTRACT_ANNOTATIONS.json'])
 for n,arg in [('registry','registry'),('entry','entry')]:
  f='validate_verifier_registry_'+('v1' if n=='registry' else 'entry_v1')
  header='pub fn '+f+'('
  attr='#[cfg_attr(kani,kani::ensures(|r| (*r == NJI_v1::'+n+'_ref('+arg+')) != cfg!(NJI_invert)))]\n#[cfg_attr(kani,kani::modifies())]\n'
  assert files[key].count(header)==1
  files[key]=files[key].replace(header,attr+header)
  anns[header]=attr
 files['NGL_CONTRACT_ANNOTATIONS.json']=json.dumps(anns)
 pins=json.loads(files['NIJ_SOURCE_PINS.json'])
 for n,t in files.items():
  if n.startswith('NIJ_src/') and not n.endswith('Cargo.lock'):pins[n[len('NIJ_src/'):]]=sha(t.encode())
 files['NIJ_SOURCE_PINS.json']=json.dumps(pins)
 manifest='/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107/NIJ_src/crates/aspis-statement/Cargo.toml'
 features=','.join(json.loads((E.parent/'slice-d-entry5-20261107/NIJ_STATEMENT_FEATURES.json').read_text()))
 cmd=x['native_command'];cmd[cmd.index('--manifest-path')+1]=manifest;cmd[cmd.index('--features')+1]=features;cmd[cmd.index('--harness')+1]='pool_v1::verifier_registry::NJI_v1::'+name+'_contract'
 if invert:x['env']['RUSTFLAGS']=x['env'].get('RUSTFLAGS','')+' --cfg NJI_invert'
 x.update(sources=list(files),module='NJI_v1::'+name+'_contract',root_package='aspis-statement',metadata_manifest=manifest,metadata_features=features,expected_time='optimized compilation then one pure full-Result validator contract',control='inverted ensures' if invert else 'positive empty-modifies contract')
 return run(a,'NIJ_K120',(x,original,files))
if __name__=='__main__':contract(sys.argv[1],sys.argv[2],len(sys.argv)>3)
