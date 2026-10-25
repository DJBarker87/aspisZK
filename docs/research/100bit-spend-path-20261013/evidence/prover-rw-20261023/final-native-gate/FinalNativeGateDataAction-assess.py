import hashlib,json,shutil,datetime
from pathlib import Path
E=Path(__file__).resolve().parent
V=Path.cwd()/'tools/prover-rw-20261023/final-native-gate/prospective-data-v3'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
outer=json.loads((E/'FinalNativeGateDataAction-transport.stdout').read_text())
packet=Path(outer['packet']);rawpins={}
for name in ('stdout','stderr','receipt.json'):
 b=(packet/name).read_bytes();rawpins[name]=pin(b)
 assert len(b)<=4*2**20
 shutil.copyfile(packet/name,E/('FinalNativeGateDataAction-primary-'+name))
r=json.loads((packet/'receipt.json').read_text());assert r['exit']==outer['exit']==1
assert r['receiver']==pin((V/'FinalNativeGate-data-transfer.py').read_bytes())
err=(packet/'stderr').read_text();assert 'line 73, in install' in err and 'transfer ancestor owner/type/permissions' in err
assert (packet/'stdout').read_bytes()==b''
status=(E/'FinalNativeGateDataAction-status.stdout').read_text()
fields=dict(line.split('=',1) for line in status.splitlines())
assert fields==dict(ControlGroup='',LoadState='not-found',ActiveState='inactive',SubState='dead',ActiveEnterTimestampMonotonic='0',InvocationID='')
rows={p.name:p.read_bytes() for p in (V/'payload').iterdir() if p.is_file()}
for name,field,source in [('FinalNativeGate_seal.py','PLAN_SHA256','FinalNativeGate-plan.json'),('FinalNativeGate_bootstrap_seal.py','BOOTSTRAP_SHA256','FinalNativeGate-bootstrap.json')]:
 assert rows[name]==(field+' = '+repr(hashlib.sha256(rows[source]).hexdigest())+'\n').encode()
boot=json.loads(rows['FinalNativeGate-bootstrap.json'])
assert set(boot)==set(rows)-{'FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py'}
for name,p in boot.items():assert pin(rows[name])==p
plan=json.loads(rows['FinalNativeGate-plan.json'])
nullfields=['cache_inventory','cache_output_bounds','catalogs','environment','host_runtime','inherited_limits','native_runtime_dependencies']
assert all(plan[k] is None for k in nullfields)
missing=[dict(role='planned-native-root',path=p,status='UNOBSERVED; collection not reached') for p in plan['native_roots']]
missing += [dict(role='Python executable/stdlib/mapped libraries',status='UNOBSERVED; dynamic runtime proposal not reached'),dict(role='existing-cache-fingerprint',path='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/resume-p6/compact/target/debug',status='UNOBSERVED; no cache selected'),dict(role='existing-cache-fingerprint',path='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/resume-mir/target/release',status='UNOBSERVED; no cache selected')]
assessment=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),claim='The single DATA receiver rejected an ancestor before mkdir/source installation/setup; the fixed unit was subsequently observed not-found/inactive/dead.',raw_primary=rawpins,primary_exit=1,primary_setup_exit=None,primary_output_JSON=False,primary_terminal_records=[],fresh_headroom=None,fresh_limits=None,fresh_role_data=None,fresh_source_or_seal_observation=None,root_seals_verified='local released payload only; no remote stage installed by this invocation',seven_final_fields_still_null=nullfields,missing_roles=missing,missing_source_dependencies='All planned target/harness/registry pin observations not reached; host absence not inferred.',closure=dict(source_path='receiver install line73 -> check_directory line28; mkdir line80 and setup main line165/169 not reached',conditional_fixed_handle=fields,established='No setup scope launched by this action; fixed unit not loaded at the single status observation',not_established=['remote ancestor identity/mode/UID causing rejection','kernel cgroup.kill write viability','general termination or D-state guarantee']),next_deliverable='Lead-authorized finite read-only ancestry metadata collection for fixed STAGE ancestors, returning exact owner/type/mode at the rejected component without config changes; review before any new DATA allocation. Do not relax checks or rerun unchanged.',source_change=False,assumptions_discharged=[],assumptions_retained=['OS','systemd','procfs','Python','bootstrap','compiler','Kani','policy'],print_axioms='N/A',main_SSH=1,conditional_status_SSH=1,all_other_SSH=0,actual_heavy_proof_nativebackend_root_compiler_cargo_Kani_Lean_extraction_ELF=0,both_deployed_security_targets='NOT ESTABLISHED')
with (E/'FinalNativeGateDataAction-assessment.json').open('x') as f:json.dump(assessment,f,sort_keys=True,indent=2)
print(json.dumps(dict(raw_primary=rawpins,status=fields,local_payload_seals_verified=True)))
