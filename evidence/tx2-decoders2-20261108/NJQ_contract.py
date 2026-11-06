"""Actual frozen decoder contracts against an independent safe reference, (ah)."""
from NJQ_rerun import *
from NJQ_patch import read_patch

def contract(a,name,invert=False):
 x,original,files=historical('NIJ_K120')
 module='NJQ_'+name
 parent='crates/aspis-statement/src/pool_v1/format.rs' if name=='identity' else 'crates/aspis-statement/src/pool_v1/verifier_registry.rs'
 key='NIJ_src/'+parent
 text=read_patch(module)
 files[key]+='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
 files['NIJ_src/'+str(Path(parent).parent/(module+'.rs'))]=text
 files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("['NIJ_entry'", "['"+module+"','NIJ_entry'")
 func={'identity':'decode_pool_identity_v1','registry':'decode_verifier_registry_v1','entry':'decode_verifier_registry_entry_v1'}[name]
 length={'identity':144,'registry':128,'entry':192}[name]
 header='pub fn '+func+'('
 check='(*r == '+module+'::decode_ref(bytes))' if name=='identity' else module+'::matches_reference(bytes,r)'
 attr='#[cfg_attr(kani,kani::requires(bytes.len()=='+str(length)+'))]\n#[cfg_attr(kani,kani::ensures(|r| '+check+' != cfg!(NJQ_invert)))]\n#[cfg_attr(kani,kani::modifies())]\n'
 assert files[key].count(header)==1;files[key]=files[key].replace(header,attr+header)
 anns=json.loads(files['NGL_CONTRACT_ANNOTATIONS.json']);anns[header]=attr;files['NGL_CONTRACT_ANNOTATIONS.json']=json.dumps(anns)
 pins=json.loads(files['NIJ_SOURCE_PINS.json'])
 for n,t in files.items():
  if n.startswith('NIJ_src/') and not n.endswith('Cargo.lock'):pins[n[len('NIJ_src/'):]]=sha(t.encode())
 files['NIJ_SOURCE_PINS.json']=json.dumps(pins)
 manifest='/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107/NIJ_src/crates/aspis-statement/Cargo.toml'
 features=','.join(json.loads((E.parent/'slice-d-entry5-20261107/NIJ_STATEMENT_FEATURES.json').read_text()))
 cmd=x['native_command'];cmd[cmd.index('--manifest-path')+1]=manifest;cmd[cmd.index('--features')+1]=features;cmd[cmd.index('--harness')+1]='pool_v1::'+('format' if name=='identity' else 'verifier_registry')+'::'+module+'::decode_contract'
 if invert:x['env']['RUSTFLAGS']=x['env'].get('RUSTFLAGS','')+' --cfg NJQ_invert'
 x.update(sources=list(files),module=module+'::decode_contract',root_package='aspis-statement',metadata_manifest=manifest,metadata_features=features,expected_time='optimized compilation then full-Result decoder contract',control='inverted ensures' if invert else 'positive empty-modifies contract')
 return run(a,'NIJ_K120',(x,original,files))
if __name__=='__main__':contract(sys.argv[1],sys.argv[2],len(sys.argv)>3)
