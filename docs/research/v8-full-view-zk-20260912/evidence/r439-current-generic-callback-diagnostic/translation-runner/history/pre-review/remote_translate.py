import datetime,hashlib,json,pathlib,re,subprocess,sys
facts=json.loads(sys.argv[1])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=pathlib.Path(facts['remote_input']); binary=pathlib.Path(facts['binary']); out=pathlib.Path(facts['remote_output'])
assert not out.exists(),f'output path exists: {out}'
assert source.is_file() and sha(source)==facts['input_sha256'],{'input':str(source),'actual':sha(source) if source.exists() else None}
assert binary.is_file() and sha(binary)==facts['binary_sha256'],{'binary':str(binary),'actual':sha(binary) if binary.exists() else None}
assert facts['binary_sha256']=='eadb205fc1e00cf7e32197dd7cbbbd82aa42b59442d8f186cfdca7c8fdca9b01'
data=json.loads(source.read_text()); assert data.get('has_errors') is False
tr=data['translated']; assert len(tr['fun_decls'])>284 and isinstance(tr['fun_decls'][284],dict), 'expected source function row 284 is absent'
mem={k:v for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
avail=int(mem['MemAvailable'].split()[0])*1024; cap=7*1024**3; reserve=24*1024**3
assert avail-cap>=reserve,{'meminfo':mem,'cap':cap,'reserve':reserve}
heavy=[]
for p in pathlib.Path('/proc').iterdir():
 if p.name.isdigit():
  try:
   comm=(p/'comm').read_text().strip()
   if comm in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4'):
    heavy.append({'pid':p.name,'comm':comm})
  except (OSError,FileNotFoundError): pass
assert not heavy,heavy
# Preserve active Aspis unit reservations as evidence and fail if their declared caps leave too little headroom.
units=[]
for line in subprocess.check_output(['systemctl','--user','list-units','--all','--plain','--state=running','--no-legend'],text=True).splitlines():
 cols=line.split()
 if not cols or not cols[0].startswith('aspis') or not cols[0].endswith(('.service','.scope')): continue
 unit=cols[0]
 props=subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryMax','-p','MemoryCurrent','-p','ControlGroup'],text=True)
 d=dict(z.split('=',1) for z in props.splitlines() if '=' in z); cg=pathlib.Path('/sys/fs/cgroup')/d.get('ControlGroup','').lstrip('/'); pids=[]
 if cg.exists():
  for f in cg.rglob('cgroup.procs'):
   try:pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
   except OSError:pass
 if pids:
  assert str(d.get('MemoryMax','')).isdigit(),('uncapped active Aspis unit',unit,d)
  units.append({'unit':unit,'pids':pids,'MemoryMax':d['MemoryMax'],'MemoryCurrent':d.get('MemoryCurrent')})
reserved=sum(int(x['MemoryMax']) for x in units)
mem_total=int(mem['MemTotal'].split()[0])*1024; safe=min(40*1024**3,mem_total-16*1024**3)
assert cap+reserved<=safe,{'cap':cap,'other_aspis_reserved':reserved,'safe_limit':safe}
out.mkdir(parents=True)
def cgroup_snapshot():
 rel=next(x.split('::',1)[1].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
 cg=pathlib.Path('/sys/fs/cgroup')/rel
 names=['memory.high','memory.max','memory.swap.max','pids.max','memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events','pids.current']
 return {'path':str(cg),**{n:(cg/n).read_text().strip() if (cg/n).exists() else None for n in names}}
before=cgroup_snapshot()
assert (before['memory.high'],before['memory.max'],before['memory.swap.max'],before['pids.max'])==('5368709120','7516192768','0','128'),before
facts_record={'input_sha256':sha(source),'binary_sha256':sha(binary),'source_revision':facts['source_revision'],'input_remote_path':str(source),'binary_path':str(binary),'remote_output':str(out),'namespace':facts['namespace'],'cgroup_before':before,'meminfo_before':mem,'active_aspis_reservations':units,'active_aspis_memory_max_bytes':reserved,'memory_safe_limit_bytes':safe,'candidate_memory_max_bytes':cap,'heavy_processes':heavy,'has_errors':False,'function_slots':len(tr['fun_decls']),'target_source_fun284_present':True,'caps':facts['caps']}
(out/'host-reservation-before.json').write_text(json.dumps(facts_record,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',facts['namespace'],'-dest',str(out/'generated'),'-subdir',facts['namespace'],'-split-files','-emit-json',str(source)]
(out/'translate-command.json').write_text(json.dumps({'command':cmd,'input_sha256':sha(source),'binary_sha256':sha(binary),'source_revision':facts['source_revision'],'namespace':facts['namespace'],'expected_manifest_def_id':284,'flags':['-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',facts['namespace'],'-dest','<fresh>/generated','-subdir',facts['namespace'],'-split-files','-emit-json']},indent=2))
with (out/'translate.log').open('wb') as log:
 run=subprocess.run(['/usr/bin/time','-v','-o',str(out/'gnu-time.txt'),*cmd],stdout=log,stderr=subprocess.STDOUT)
after=cgroup_snapshot(); generated=out/'generated'; manifest=generated/'translation.json'; md=json.loads(manifest.read_text()) if manifest.is_file() else {}; funcs=md.get('functions',[])
root_rows=[f for f in funcs if f.get('def_id')==284]
external={}
for p in sorted(generated.rglob('*')) if generated.is_dir() else []:
 if p.is_file() and p.name.endswith('_External_Template.lean'):
  external[str(p.relative_to(generated))]=re.findall(r'^axiom\s+([^\s(]+)',p.read_text(errors='replace'),re.M)
files={str(p.relative_to(out)):sha(p) for p in sorted(generated.rglob('*')) if p.is_file()} if generated.is_dir() else {}
gtxt=(out/'gnu-time.txt').read_text(errors='replace') if (out/'gnu-time.txt').is_file() else ''
def metric(pattern,cast=str):
 m=re.search(pattern,gtxt,re.M); return cast(m.group(1).strip()) if m else None
translation={'translator_exit_status':run.returncode,'generated_dir_exists':generated.is_dir(),'translation_json_exists':manifest.is_file(),'manifest_function_entries':len(funcs),'manifest_root_def_id_284_matches':len(root_rows),'manifest_root_def_id_284_rows':root_rows,'external_template_axiom_names':external,'generated_file_sha256':files,'warning_lines':[x for x in (out/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in x]}
(out/'translation-result.json').write_text(json.dumps(translation,indent=2))
result={'translator_exit_status':run.returncode,'input_sha256':sha(source),'binary_sha256':sha(binary),'source_revision':facts['source_revision'],'namespace':facts['namespace'],'target_function_row':284,'translation':translation,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'),'peak_rss_kib':metric(r'Maximum resident set size \(kbytes\):\s*(\d+)',int),'swap_count':metric(r'Swaps:\s*(\d+)',int),'gnu_time_exit_status':metric(r'Exit status:\s*(\d+)',int),'cgroup_before':before,'cgroup_after':after,'meminfo_after':{k:v for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},'scope':'Focused translation inventory only. No Lean compilation, template fill, execution equivalence, or source/security claim.'}
(out/'result.json').write_text(json.dumps(result,indent=2))
print(json.dumps({'translator_exit_status':run.returncode,'wall_time':result['wall_time'],'peak_rss_kib':result['peak_rss_kib'],'swap_count':result['swap_count'],'manifest_root_284_matches':len(root_rows),'generated_files':len(files)}))
sys.exit(run.returncode)
