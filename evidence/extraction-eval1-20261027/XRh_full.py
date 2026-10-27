from pathlib import Path
import subprocess,os,json,hashlib,sys,time,re
B=Path(__file__).resolve().parent
S=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src')
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
case=sys.argv[1]
groups={'shared':['crate::compact::check_values'],'distinct':['crate::verifier::echeck'],'context':['crate::verifier::checkpoint'],'borrow':['crate::compact::expand_values','crate::verifier::candidate::wide_view','crate::fast_pairing::canonical::_::push','crate::sampler::circle_sample'],'arrow':['crate::r1_semantic::semantic_boundary'],'full':['crate::verifier::candidate::tx1']}
roots=groups[case]
pins=json.loads((O/'XRa_release_sourcepins.json').read_text());bad=[]
for r in pins['files']:
 p=S/r['path']
 if not p.is_file() or hashlib.file_digest(p.open('rb'),'sha256').hexdigest()!=r['sha256']:bad.append(r['path'])
assert not bad,bad
C=B/'XRh_charon_target/release/charon';A=B/'XRh_new_aeneas/src/_build/default/main.exe'
llbc=B/('XRh_'+case+'.llbc');out=B/('XRh_new_generated_'+case)
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--include','core::cmp::PartialEq::ne','--duplicate-defaulted-methods']
# Full evaluation expands every reached in-repo dependency body; std remains pinned backend library.
if case=='full':
 for dep in ['aspis_core','aspis_statement','aspis_r0_writer_copies','aspis_r0_block_writer_copies','aspis_r0_poseidon_copy']:
  cmd+=['--include',dep]
# Same two common bodies are included in shared probe to measure carrier and dictionary deltas.
if case=='shared':roots=roots+['crate::verifier::candidate::same_batch_index','crate::verifier::candidate::batch_leaf']
for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--no-default-features','--features','private-leaf-salts','--jobs','1']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'XRh_release_target'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RAYON_NUM_THREADS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(k,None)
def h(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
r=dict(case=case,roots=roots,release_revision=pins['source_revision'],release_files_checked=len(pins['files']),changed_release_files=bad,charon_sha256=h(C),aeneas_sha256=h(A),charon_command=cmd,opaque_selectors=[],experimental_only=True)
print('CHARON_COMMAND',json.dumps(cmd),flush=True);t=time.monotonic()
x=subprocess.run(['/usr/bin/time','-v','-o',str(B/('XRh_'+case+'_charon.time')), *cmd],cwd=S,env=env)
r.update(charon_exit=x.returncode,charon_wall=time.monotonic()-t)
if x.returncode:
 (B/('XRh_'+case+'_result.json')).write_text(json.dumps(r,indent=2)+'\n');raise SystemExit(x.returncode)
v=json.loads(llbc.read_text());r.update(llbc_sha256=h(llbc),llbc_bytes=llbc.stat().st_size,has_errors=v.get('has_errors'))
project=[]
for f in v['translated']['fun_decls']:
 if f is None:continue
 ids=[x['Ident'][0] for x in f['item_meta']['name'] if 'Ident' in x]
 if ids and ids[0].startswith('aspis_') and f.get('body')=='Opaque':
  project.append(dict(id=f['def_id'],name=f['item_meta']['name'],idents='::'.join(ids),span=f['item_meta']['span'],src=f.get('src')))
r['opaque_project_functions']=project
r['non_digest_opaque_project_functions']=[x for x in project if x['idents']!='aspis_core::digest::Digest32::digest']
(B/('XRh_'+case+'_result.json')).write_text(json.dumps(r,indent=2)+'\n')
assert not v.get('has_errors'),v.get('has_errors')
assert not r['non_digest_opaque_project_functions'],r['non_digest_opaque_project_functions']
cmd=[str(A),'-log','Translate','-sequential','-no-progress-bar','-backend','lean','-namespace','XRh_Eval','-dest',str(out),'-subdir','XRh_Eval','-split-files','-emit-json',str(llbc)]
r['aeneas_command']=cmd
print('AENEAS_COMMAND',json.dumps(cmd),flush=True);t=time.monotonic()
x=subprocess.run(['/usr/bin/time','-v','-o',str(B/('XRh_'+case+'_aeneas.time')), *cmd])
r.update(aeneas_exit=x.returncode,aeneas_wall=time.monotonic()-t,outputs=[dict(path=str(p),sha256=h(p),bytes=p.stat().st_size) for p in sorted(out.rglob('*')) if p.is_file()])
(B/('XRh_'+case+'_result.json')).write_text(json.dumps(r,indent=2)+'\n');print('RESULT',json.dumps(r),flush=True)
raise SystemExit(x.returncode)
