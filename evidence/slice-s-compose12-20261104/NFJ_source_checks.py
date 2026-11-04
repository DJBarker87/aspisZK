"""Frozen cut review, including same allocation/slot and both continuations."""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P='programs/r1-cost-probe/src/r1_pool_adapter.rs';F=P+'::scan_proof_buffer'
sha=lambda b:hashlib.sha256(b).hexdigest()
def frozen_body(text=None):
 if text is None:text=subprocess.check_output(['git','show',REV+':'+P],text=True)
 start=text.index('fn scan_proof_buffer(');return text[start:text.index('\n}',start)+2]
def review(text=None):
 f=frozen_body(text)
 assert sha(f.encode())=='1c707dc3697a293d55ab884cc0780d57ac500bc3a60990fff53a1d8c9efa9440'
 expected='''    if encode_pool_v1_pair_verified_afterstate_v1(&candidate)
        .map_err(|_| ProgramError::InvalidAccountData)?
        .as_ref()
        != candidate_bytes
        || bytes[proof_start + 8] != Variant::S2.tag()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(ScannedAsqaProof {
        candidate_afterstate: candidate,
        proof_length,
    })'''
 assert expected in f
 assert 'let candidate_start = 0;' in f and 'let proof_start = candidate_start + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;' in f
 assert 'let candidate_bytes = &bytes[candidate_start..proof_start];' in f
 assert f.count('encode_pool_v1_pair_verified_afterstate_v1(')==1 and f.count('decode_pool_v1_pair_verified_afterstate_v1(')==1 and f.count('Variant::S2.tag()')==1
 return dict(frozen_body_sha256=sha(f.encode()),comparison_expression=expected,retained_reply='successful fixed [u8;688] encoder reply before .as_ref()',retained_header='same bytes[0..688] allocation',slot_observer='slot != 0 only',same_continuations=True)

SOURCE_HASHES={'NFJ_K003': 'd7bc2a86da84a6755bbad72781be7985e7c7368c3a44fb4317cca44785c59836', 'NFJ_K004': '1a784bace36522f23e3dbcf919e9bc48b83a6eccf3523ff94bebc1a7543752d1', 'NFJ_K005': '403895aaf46f666416bd14336a13ffa71f7a9896ba2c86be16fde4acddffc697', 'NFJ_K006': '60be81e084bd5b6907849162325f6af11b5914bbd27ad3d8f9017debd8501558', 'NFJ_K007': 'bed76fcdbd46c7e6ef54149b1bc1a191ea44cd9c2be8ee5ccad28fccfc60f3f7', 'NFJ_K008': '7326a12da5c7d34655d374c9aced1b1e9f43a99b11a527a12b89805f3f7999fb', 'NFJ_K009': 'b18ebed31635e8df2f3127941108e7d44f5094153cfe9e4f473485d94032a2a0', 'NFJ_K010': '38bc7301bbe4a6e5eea15e2f2818504bb252e4a16cc2b2bf795dbffbf222c1e1', 'NFJ_K011': '73082637ac8200aee199bd0130ce3ba6a10ae1c8795e2c77375c0eb6cbb7ba9c', 'NFJ_K012': '9cfa010624f8b3b98f42401ca0e07aeef0f72397b0fafc66681fbdfcafb4a7b3', 'NFJ_K013': '446c94ce2e8cd547739658668117768d90af012233c96d6ad0917c24abefc384', 'NFJ_K014': '98a81c5e9bb969bbd1c66bef196a7ce47d026988dabd6b012ed85d948cc23797'}
def native(a,positive):
 r=json.loads((E/a/'receipt.json').read_text());cfg=json.loads((E/(a+'.json')).read_text());m=json.loads((E/(a+'-shape.json')).read_text())
 assert r['exit_status']==(0 if positive else 1) and r['kind']=='kani'
 assert r['source_revision'] and float(r['wall_seconds'])>0 and int(r['peak_rss_kib'])>0 and int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert all(r[k]==v for k,v in cfg.items())
 assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert '--locked' not in cfg['native_command'] and cfg['native_command'][cfg['native_command'].index('--harness-timeout')+1]=='90s'
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for suffix,key in [('graph-check','exact_LPm_graph'),('lock-check','unchanged'),('rule16-check','no_writable_static')]:assert json.loads((E/(a+'-'+suffix+'.json')).read_text())[key] is True
 assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
 assert cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in log) is positive
 assert positive or 'Failed Checks:' in log
 assert not any(t in log.lower() for t in ['timed out','out of memory'])
 source=m['source'];assert sha(source.encode())==SOURCE_HASHES[a];patch=(E/(a+'-NFJ_native.patch')).read_text()
 assert source in ''.join(l[1:]+'\n' for l in patch.splitlines() if l.startswith('+') and not l.startswith('+++'))
 assert not any(x in source for x in ['static mut','stub_verified','Option<fn','transmute','Atomic','UnsafeCell'])
 assert r['source_hashes']['NFJ_native.patch']==sha(patch.encode())
 assert r['source_hashes']['NFJ_kani_gate.py']==sha((E/'NFJ_kani_gate.py').read_bytes())
 identity=json.loads((E/(a+'-frozen-identity.json')).read_text());assert identity['exact_frozen_plus_patches'] is True and identity['frozen_revision']==REV
 assert r['source_hashes']['NFJ_RUST_SHA256.json']==sha(json.dumps(identity['manifest']).encode())
 sys.path.insert(0,str(E.parent/'slice-s-compose10-20261104'))
 from NFD_frozen_identity import frozen,apply
 files=dict(frozen());files.update({n:v.encode() for n,v in json.loads((E/'NFJ_INCLUDES.json').read_text()).items()})
 for p in ['NFJ_KMX_copy_stubs.patch','NFJ_contract_controls.patch']:apply(files,(E/p).read_text())
 apply(files,patch)
 assert identity['manifest']=={n:sha(v) for n,v in files.items()}
 fs={p['name']:set(p['features']) for p in json.loads((E/(a+'-metadata-pin.json')).read_text())['features_all_crates']}
 assert {'pool-adapter','private-leaf-salts'}<=fs['aspis-r1-cost-probe-program'] and not {'no-entrypoint','cu-profiling'}&fs['aspis-r1-cost-probe-program']
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=fs['aspis-r1-cost-probe'] and set(cfg['required_statement_features'])<=fs['aspis-statement']
 return m

def all_native():
 expected={3:'positive',4:'left',5:'right',6:'size',7:'slot',8:'reply',9:'branch',10:'frame',11:'copy',12:'copy-negative',13:'header',14:'header-negative'}
 for n,mode in expected.items():assert native(f'NFJ_K{n:03}',mode in ['positive','copy','header'])['mode']==mode
 # Exact source, not mere evidence flags. Regeneration is pure and reviewed by hash.
 source=json.loads((E/'NFJ_K003-shape.json').read_text())['source']
 assert 'runtime(left,right,688,&mut slot,f);\n slot!=0' in source
 assert 'different(encoded.as_ref(),candidate_bytes,f) || tag!=Variant::S2.tag()' in source
 assert 'f.slot=&mut slot;' in source and '*slot=f.reply;' in source
 assert source.count('slot!=0')==1
 return review()
