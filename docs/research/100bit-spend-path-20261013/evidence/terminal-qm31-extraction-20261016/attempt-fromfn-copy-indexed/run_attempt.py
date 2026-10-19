#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys,time,copy
from pathlib import Path
ATTEMPT=Path(__file__).resolve().parent
KIT=ATTEMPT/'input'
BASE=Path('/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016/attempt-f-row-helper/input')
TARGET=Path('/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016/attempt-d/target')
RUSTUP=Path('/home/dombarker/.cargo/bin/rustup')
CARGO=Path('/home/dombarker/.cargo/bin/cargo')
CHARON=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
AENEAS=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas')
TOOLCHAIN='nightly-2026-06-01'
LIMITS={'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':'0','TasksMax':'128'}
ENV={**os.environ,'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':TOOLCHAIN,'CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes','CARGO_TARGET_DIR':str(TARGET),'CARGO_NET_OFFLINE':'true'}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def preflight():
 base=json.loads((BASE/'merged-source-manifest.json').read_text())
 meta=json.loads((ATTEMPT/'candidate-source-manifest.json').read_text())
 if sha(BASE/'merged-source-manifest.json')!='cc3ca00c56efc58d34f3dbabee9fd52900d3d7b0e9f44675f2e493582b7d6a24':raise SystemExit('base manifest pin mismatch')
 if meta['base_source_revision']!=base['source_revision']:raise SystemExit('base revision mismatch')
 allowed={'src/statement/state_only_poseidon.rs','src/statement/pool_v1/pair_forest_semantic_terminal.rs'};diffs=[]
 rows={r['merged_path']:r for r in meta['source_files']}
 if len(rows)!=len(base['source_files']):raise SystemExit('source row count mismatch')
 for r in base['source_files']:
  rel=r['merged_path'];p=KIT/rel
  if rel not in rows or not p.is_file() or sha(p)!=rows[rel]['candidate_sha256']:raise SystemExit('candidate source hash mismatch '+rel)
  if sha(p)!=r['sha256']:
   diffs.append(rel)
   if rel not in allowed:raise SystemExit('unexpected modified source '+rel)
 if set(diffs)!=allowed:raise SystemExit('expected exactly two changed source rows '+repr(diffs))
 for f in ['Cargo.toml','Cargo.lock','build.rs']:
  if sha(KIT/f)!=sha(BASE/f):raise SystemExit('scaffold/lock changed '+f)
 helper=('\n/// Extraction-only safe fixed-array constructor for Copy outputs.\n/// Calls f in increasing index order and threads the FnMut state normally.\n#[inline(always)]\npub(crate) fn array_from_fn_copy<T: Copy, const N: usize>(\n    init: T,\n    mut f: impl FnMut(usize) -> T,\n) -> [T; N] {\n    let mut out = [init; N];\n    let mut i = 0usize;\n    while i < N {\n        out[i] = f(i);\n        i += 1;\n    }\n    out\n}\n').encode()
 rootbase=(BASE/'src/lib.rs').read_bytes(); rootcand=(KIT/'src/lib.rs').read_bytes()
 if rootcand!=rootbase.replace(b'extern crate alloc;\n',b'extern crate alloc;\n'+helper):raise SystemExit('extraction crate root differs beyond helper insertion')
 count=sum((KIT/p).read_bytes().count(b'crate::array_from_fn_copy::<_, ') for p in ['src/statement/state_only_poseidon.rs','src/statement/pool_v1/pair_forest_semantic_terminal.rs'])
 if count!=18:raise SystemExit('expected 18 call sites, got '+str(count))
 if sha(KIT/'Cargo.lock')!='e1ff38c257fe01c028da4dfecba548f9276ceb587d35e33decafa4b72f5dd359':raise SystemExit('lock hash mismatch')
 for p,h in [(CHARON,'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'),(AENEAS,'959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3')]:
  if sha(p)!=h:raise SystemExit('tool hash mismatch '+str(p))
 rustc=subprocess.check_output([str(RUSTUP),'run',TOOLCHAIN,'rustc','--version','--verbose'],text=True)
 if '1.98.0-nightly' not in rustc or '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' not in rustc:raise SystemExit('rustc pin mismatch')
 cargo=subprocess.run([str(CARGO),'metadata','--manifest-path',str(KIT/'Cargo.toml'),'--no-deps','--format-version','1','--offline','--locked'],cwd=KIT,env=ENV,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 if cargo.returncode:raise SystemExit('locked metadata failed '+cargo.stderr)
 (ATTEMPT/'cargo-metadata.json').write_text(cargo.stdout+'\n')
 receipt={'status':'pass','base_manifest_sha256':sha(BASE/'merged-source-manifest.json'),'base_source_revision':base['source_revision'],'candidate_manifest_sha256':sha(ATTEMPT/'candidate-source-manifest.json'),'candidate_changed_source_rows':diffs,'source_row_count':len(rows),'from_fn_replacements':count,'lock_sha256':sha(KIT/'Cargo.lock'),'root_helper_base_sha256':sha(BASE/'src/lib.rs'),'root_helper_candidate_sha256':sha(KIT/'src/lib.rs'),'rustc':rustc,'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),'cargo_target_dir':str(TARGET),'environment':{k:ENV[k] for k in ['RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_PROFILE_RELEASE_OPT_LEVEL','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','RUSTFLAGS','CARGO_TARGET_DIR','CARGO_NET_OFFLINE']}}
 (ATTEMPT/'preflight.json').write_text(json.dumps(receipt,indent=2)+'\n')
def reservation_snapshot(stage):
    units_out=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True)
    scopes=[]
    active_bytes=0
    for line in units_out.splitlines():
        parts=line.split()
        if not parts: continue
        unit=parts[0]
        props=subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','ControlGroup','-p','MainPID'],text=True)
        d=dict(x.split('=',1) for x in props.splitlines() if '=' in x)
        scopes.append({'unit':unit,**d})
        if unit=='init.scope': continue
        raw=d.get('MemoryMax','infinity')
        if raw=='infinity': raise SystemExit('unbounded active scope; refusing launch: '+unit)
        active_bytes += int(raw)
    reserve_bytes=24*1024**3 + 6*1024**3 + active_bytes
    current_path=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/memory.current')
    current=int(current_path.read_text().strip()) if current_path.exists() else None
    target_cmds=subprocess.check_output(['ps','-eo','args'],text=True).splitlines()
    writers=[x for x in target_cmds if str(TARGET) in x and re.search(r'(^|/)(cargo|rustc|charon|aeneas)( |$)',x)]
    rec={'utc':subprocess.check_output(['date','-u','+%FT%TZ'],text=True).strip(),'stage':stage,'active_scopes':scopes,'active_finite_memory_max_bytes_excluding_init':active_bytes,'external_reservation_bytes':24*1024**3,'this_pipeline_reservation_bytes':6*1024**3,'projected_total_bytes':reserve_bytes,'policy_limit_bytes':50*1024**3,'user_service_memory_current_bytes':current,'shared_target_active_writers':writers,'check':'pass' if reserve_bytes<=50*1024**3 and not writers else 'fail'}
    out=ATTEMPT/'reservations'/f'{stage}.json';out.parent.mkdir(exist_ok=True);out.write_text(json.dumps(rec,indent=2)+'\n')
    if rec['check']!='pass': raise SystemExit('reservation/target-writer preflight failed for '+stage)

def inside():
 name=sys.argv[2];cmd=json.loads(sys.argv[3]);log=ATTEMPT/'logs'/f'{name}.log';recp=ATTEMPT/'receipts'/f'{name}.json'
 log.parent.mkdir(exist_ok=True);recp.parent.mkdir(exist_ok=True)
 t0=time.monotonic();wall=time.time()
 with log.open('x') as f:p=subprocess.run(['/usr/bin/time','-v','timeout','--signal=KILL','300',*cmd],cwd=KIT,env=ENV,stdout=f,stderr=subprocess.STDOUT)
 elapsed=time.monotonic()-t0;text=log.read_text(errors='replace')
 cg=''
 for line in Path('/proc/self/cgroup').read_text().splitlines():
  if line.startswith('0::'):cg=line[3:];break
 cgr=Path('/sys/fs/cgroup')/cg.lstrip('/')
 def rd(k):
  try:return(cgr/k).read_text().strip()
  except:return None
 mr=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',text);mw=re.search(r'Elapsed \(wall clock\) time .*?:\s*([0-9:.]+)',text)
 rec={'stage':name,'command':cmd,'exit_status':p.returncode,'wall_seconds_monotonic':round(elapsed,3),'usr_bin_time_wall':mw.group(1) if mw else None,'peak_process_rss_kib':int(mr.group(1)) if mr else None,'cgroup':cg,'cgroup_memory_peak_bytes':rd('memory.peak'),'cgroup_memory_swap_peak_bytes':rd('memory.swap.peak'),'cgroup_memory_swap_current_bytes':rd('memory.swap.current'),'cgroup_memory_events':rd('memory.events'),'cgroup_memory_high':rd('memory.high'),'cgroup_memory_max':rd('memory.max'),'cgroup_memory_swap_max':rd('memory.swap.max'),'cgroup_pids_max':rd('pids.max'),'declared_scope_limits':LIMITS,'time_started_unix':wall,'candidate_manifest_sha256':sha(ATTEMPT/'candidate-source-manifest.json'),'runner_sha256':sha(Path(__file__))}
 recp.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);sys.exit(p.returncode)
def adapted_llbc():
 source=ATTEMPT/'output/Terminal.llbc'; dest=ATTEMPT/'output/Terminal-name-adapt.llbc'
 if sha(source)=='' or dest.exists():raise SystemExit('missing LLBC or refusing overwrite')
 original=json.loads(source.read_bytes()); adapted=copy.deepcopy(original)
 candidates=[]
 for i,f in enumerate(adapted.get('translated',{}).get('fun_decls',[])):
  if not isinstance(f,dict):continue
  m=f.get('item_meta') or {};name=m.get('name') or []
  comps=[]
  for x in name:
   if isinstance(x,dict) and 'Ident' in x and isinstance(x['Ident'],list): comps.append(x['Ident'][0])
   else: comps.append('')
  span=m.get('span',{}).get('data',{});beg=span.get('beg',{})
  if comps[-2:]==['field','M31'] and beg.get('line')==23:
   candidates.append((i,m,comps))
 if len(candidates)!=1:raise SystemExit('expected unique field::M31 constructor by source name/span, got '+str(len(candidates)))
 i,m,selected_name_components=candidates[0];info=m.get('attr_info')
 if not isinstance(info,dict) or info.get('rename') is not None:raise SystemExit('constructor rename metadata not null')
 info['rename']='M31_constructor'
 back=copy.deepcopy(adapted);back['translated']['fun_decls'][i]['item_meta']['attr_info']['rename']=None
 if back!=original:raise SystemExit('LLBC adapter changed more than one rename metadata field')
 dest.write_text(json.dumps(adapted,separators=(',',':'))+'\n')
 receipt={'original':str(source),'original_sha256':sha(source),'adapted':str(dest),'adapted_sha256':sha(dest),'function_id':adapted['translated']['fun_decls'][i].get('def_id'),'selected_name_components':selected_name_components,'selected_span':m['span'],'only_changed_json_path':f'translated.fun_decls[{i}].item_meta.attr_info.rename','old_value':None,'new_value':'M31_constructor','deep_reverse_transform_equal':True}
 (ATTEMPT/'output/name-adapter.json').write_text(json.dumps(receipt,indent=2)+'\n')
 return dest
if __name__=='__main__':
 if len(sys.argv)>1 and sys.argv[1]=='inside':inside()
 preflight()
 if len(sys.argv)>1 and sys.argv[1]=='--preflight':
  print((ATTEMPT/'preflight.json').read_text());sys.exit(0)
 (ATTEMPT/'output').mkdir(exist_ok=True)
 cmds={'build':[str(CARGO),'build','--manifest-path',str(KIT/'Cargo.toml'),'--package','aspis-r1-mask-extraction-probe','--features','r0,pool-v1-kernel','--no-default-features','--release','--locked','--offline','--lib'],
 'charon':[str(CHARON),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::extraction_probe::terminal_qm31_probe','--dest-file',str(ATTEMPT/'output/Terminal.llbc'),'--','--manifest-path',str(KIT/'Cargo.toml'),'--package','aspis-r1-mask-extraction-probe','--features','r0,pool-v1-kernel','--no-default-features','--release','--lib','--locked','--offline'],
 'aeneas':[str(AENEAS),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1SelectedMaskProbe','-dest',str(ATTEMPT/'output/generated'),'-subdir','AspisR1SelectedMaskProbe','-split-files','-emit-json','-print-unknown-externals','-loops-to-rec']}
 for name,cmd in cmds.items():
  reservation_snapshot(name)
  if name=='aeneas':
   llbc=adapted_llbc();cmd.append(str(llbc))
  base=['systemd-run','--user','--scope','--quiet','--unit='+f'aspis-terminal-fromfn-copy-indexed-{name}-20261016']
  for k,v in LIMITS.items():base+=['--property='+k+'='+v]
  base += [sys.executable,str(Path(__file__).resolve()),'inside',name,json.dumps(cmd,separators=(',',':'))]
  outer=subprocess.run(base,cwd=ATTEMPT,env=ENV,text=True,capture_output=True,timeout=360)
  (ATTEMPT/'scope-launches').mkdir(exist_ok=True)
  (ATTEMPT/'scope-launches'/f'{name}.json').write_text(json.dumps({'stage':name,'systemd_run_argv':base,'exit_status':outer.returncode,'stdout':outer.stdout,'stderr':outer.stderr,'scope_limits':LIMITS},indent=2)+'\n')
  print(json.dumps({'stage':name,'exit_status':outer.returncode,'stdout':outer.stdout,'stderr':outer.stderr}),flush=True)
  if outer.returncode:raise SystemExit(outer.returncode)
 print('build, Charon, Aeneas exited zero; target audit remains required')
