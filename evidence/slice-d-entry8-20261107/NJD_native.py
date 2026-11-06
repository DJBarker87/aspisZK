"""New native packets in the single owned scratch workspace; no shared edits."""
from NJD_rerun import *
def fresh(a,target,sidecars):
    x,original,files=historical('NIJ_K120')
    files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("['NIJ_entry'","['NJD_lane','NJD_stages','NJD_accounts','NJD_sdk','NJD_prefix','NJD_v1','NJD_active','NJD_forward','NJD_auth','NJD_owned','NIJ_entry'")
    for parent,module,text in sidecars:
        suffix='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
        key='NIJ_src/'+parent
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
    x.update(packet_mode='FRESH_NATIVE_NOT_HISTORICAL_REPLAY',expected_time='optimized compilation and one named scalar/descriptor/staged native packet')
    return run(a,'NIJ_K120',(x,original,files))
if __name__=='__main__':
    a,target=sys.argv[1:]
    fresh(a,target,[('crates/aspis-statement/src/pool_v1/verifier_registry.rs','NJD_active',''.join(l[1:] for l in (E/'NJD_active.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++')))])
