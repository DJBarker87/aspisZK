"""New native packets in the single owned scratch workspace; no shared edits."""
from NJQ_rerun import *
def fresh(a,target,sidecars,invert=False):
    x,original,files=historical('NIJ_K120')
    files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("['NIJ_entry'","['NJQ_shape','NJQ_length_cut','NJQ_checkpoint_step','NJQ_master_cut','NJQ_checkpoint_cut','NJQ_registry_cut','NJQ_entry_cut','NJQ_policy_cut','NJQ_policy','NJQ_accounts','NJQ_v1','NJQ_decoder','NJQ_active','NIJ_entry'")
    for _,own_module,_ in sidecars:
        files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("for module in [","for module in ['"+own_module+"',")
    for parent,module,text in sidecars:
        suffix='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
        key='NIJ_src/'+parent
        if key not in files:
            raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+parent]);assert sha(raw)==json.loads(files['NIJ_SOURCE_PINS.json'])[parent];files[key]=raw.decode()
        files[key]+=suffix
        files['NIJ_src/'+str(Path(parent).parent/(module+'.rs'))]=text
    pins=json.loads(files['NIJ_SOURCE_PINS.json'])
    for n,t in files.items():
        if n.startswith('NIJ_src/') and not n.endswith('Cargo.lock'):pins[n[len('NIJ_src/'):]]=sha(t.encode())
    files['NIJ_SOURCE_PINS.json']=json.dumps(pins)
    x['sources']=list(files)
    x['native_command'][x['native_command'].index('--harness')+1]=target.removeprefix('statement:')
    x['module']=target
    if target.startswith('statement:'):
        manifest='/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107/NIJ_src/crates/aspis-statement/Cargo.toml'
        features=json.loads((E.parent/'slice-d-entry5-20261107/NIJ_STATEMENT_FEATURES.json').read_text())
        x['native_command'][x['native_command'].index('--manifest-path')+1]=manifest
        x['native_command'][x['native_command'].index('--features')+1]=','.join(features)
        x.update(root_package='aspis-statement',metadata_manifest=manifest,metadata_features=','.join(features))
    if invert:x['env']['RUSTFLAGS']=x['env'].get('RUSTFLAGS','')+' --cfg NJQ_invert'
    x.update(packet_mode='FRESH_NATIVE_NOT_HISTORICAL_REPLAY',expected_time='optimized compilation and one named scalar/descriptor/staged native packet')
    return run(a,'NIJ_K120',(x,original,files))
if __name__=='__main__':
    a,target=sys.argv[1:]
    fresh(a,target,[('crates/aspis-statement/src/pool_v1/verifier_registry.rs','NJQ_active',''.join(l[1:] for l in (E/'NJQ_active.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++')))])
