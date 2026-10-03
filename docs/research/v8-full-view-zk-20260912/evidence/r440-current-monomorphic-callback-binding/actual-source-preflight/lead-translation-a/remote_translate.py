#!/usr/bin/env python3
"""Focused R440 Aeneas translation; input and source revision require lead approval."""
import hashlib,json,pathlib,re,subprocess,sys
facts=json.loads(sys.argv[1])
UNIT='aspis-r440-gamma-execution-translation'
assert facts.get('unit')==UNIT
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=pathlib.Path(facts['remote_input']); binary=pathlib.Path(facts['binary']); out=pathlib.Path(facts['remote_output'])
assert not out.exists(),f'output path exists: {out}'
assert source.is_file() and sha(source)==facts['input_sha256'],{'input':str(source),'actual':sha(source) if source.exists() else None}
assert binary.is_file() and sha(binary)==facts['binary_sha256'],{'binary':str(binary),'actual':sha(binary) if binary.exists() else None}
assert facts['binary_sha256']=='eadb205fc1e00cf7e32197dd7cbbbd82aa42b59442d8f186cfdca7c8fdca9b01'
data=json.loads(source.read_text()); assert data.get('has_errors') is False
tr=data['translated']; rows=tr.get('fun_decls',[]); ordered=tr.get('ordered_decls',[])
roots=[29,70,112]
assert len(rows)>max(roots) and all(isinstance(rows[i],dict) for i in roots),'expected Fun29/Fun70/Fun112 source rows absent'
ordered_fun_ids={x['Fun']['NonRec'] for x in ordered if isinstance(x,dict) and 'Fun' in x and isinstance(x['Fun'],dict) and 'NonRec' in x['Fun']}
assert set(roots)<=ordered_fun_ids,'one or more required function roots absent from ordered_decls'
assert len(ordered)==62,'unexpected projected declaration count'
assert facts['expected_projection_sha256']=='96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48'
assert facts['expected_native_roots']==roots
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
# Count active capped Aspis reservations across both managers once per cgroup.
units=[]; counted=set(); reserved=0
for manager,label in ((['systemctl','--user'],'user'),(['systemctl'],'system')):
 listing=subprocess.check_output(manager+['list-units','--all','--plain','--state=running','--no-legend'],text=True)
 for line in listing.splitlines():
  cols=line.split()
  if not cols or not cols[0].startswith('aspis') or not cols[0].endswith(('.service','.scope')): continue
  unit=cols[0]
  if unit==UNIT+'.service': continue
  props=subprocess.check_output(manager+['show',unit,'-p','MemoryMax','-p','MemoryCurrent','-p','ControlGroup'],text=True)
  d=dict(z.split('=',1) for z in props.splitlines() if '=' in z)
  cgname=d.get('ControlGroup',''); cg=pathlib.Path('/sys/fs/cgroup')/cgname.lstrip('/'); pids=[]
  if cg.exists():
   for f in cg.rglob('cgroup.procs'):
    try:pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
    except OSError:pass
  pids=sorted(set(pids)); raw=d.get('MemoryMax',''); finite=raw.isdigit() and int(raw)>0
  if pids:
   assert finite,('uncapped active Aspis unit',label,unit,d)
   if cgname not in counted:
    reserved+=int(raw); counted.add(cgname)
   units.append({'manager':label,'unit':unit,'control_group':cgname,'pids':pids,'MemoryMax':raw,'MemoryCurrent':d.get('MemoryCurrent'),'counted':cgname in counted})
mem_total=int(mem['MemTotal'].split()[0])*1024; safe=min(40*1024**3,mem_total-16*1024**3)
assert cap+reserved<=safe,{'cap':cap,'other_aspis_reserved':reserved,'safe_limit':safe,'units':units}
out.mkdir(parents=True)
def cgroup_snapshot():
 rel=next(x.split('::',1)[1].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
 cg=pathlib.Path('/sys/fs/cgroup')/rel
 names=['memory.high','memory.max','memory.swap.max','pids.max','memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events','pids.current']
 return {'path':str(cg),**{n:(cg/n).read_text().strip() if (cg/n).exists() else None for n in names}}
before=cgroup_snapshot()
assert (before['memory.high'],before['memory.max'],before['memory.swap.max'],before['pids.max'])==('5368709120','7516192768','0','128'),before
facts_record={'input_sha256':sha(source),'expected_projection_sha256':facts['expected_projection_sha256'],'binary_sha256':sha(binary),'source_revision':facts['source_revision'],'projection_source_revision':facts['projection_source_revision'],'input_remote_path':str(source),'binary_path':str(binary),'remote_output':str(out),'namespace':facts['namespace'],'cgroup_before':before,'meminfo_before':mem,'active_aspis_reservations':units,'deduplicated_reserved_memory_max_bytes':reserved,'counted_cgroups':sorted(counted),'memory_safe_limit_bytes':safe,'candidate_memory_max_bytes':cap,'heavy_processes':heavy,'has_errors':False,'fun_decl_slots':len(rows),'ordered_declarations':len(ordered),'required_native_roots':roots,'required_native_roots_present':True,'caps':facts['caps']}
(out/'host-reservation-before.json').write_text(json.dumps(facts_record,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',facts['namespace'],'-dest',str(out/'generated'),'-subdir',facts['namespace'],'-split-files','-emit-json',str(source)]
(out/'translate-command.json').write_text(json.dumps({'command':cmd,'input_sha256':sha(source),'expected_projection_sha256':facts['expected_projection_sha256'],'binary_sha256':sha(binary),'source_revision':facts['source_revision'],'projection_source_revision':facts['projection_source_revision'],'namespace':facts['namespace'],'required_native_roots':roots,'ordered_declarations_expected':62,'flags':['-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',facts['namespace'],'-dest','<fresh>/generated','-subdir',facts['namespace'],'-split-files','-emit-json']},indent=2))
with (out/'translate.log').open('wb') as log:
 run=subprocess.run(['/usr/bin/time','-v','-o',str(out/'gnu-time.txt'),*cmd],stdout=log,stderr=subprocess.STDOUT)
after=cgroup_snapshot(); generated=out/'generated'; manifest=generated/'translation.json'; md=json.loads(manifest.read_text()) if manifest.is_file() else {}; funcs=md.get('functions',[])
root_rows={str(i):[f for f in funcs if f.get('def_id')==i] for i in roots}
external={}
for p in sorted(generated.rglob('*')) if generated.is_dir() else []:
 if p.is_file() and p.name in ('FunsExternal_Template.lean','TypesExternal_Template.lean'):
  external[str(p.relative_to(generated))]=re.findall(r'^axiom\s+([^\s(]+)',p.read_text(errors='replace'),re.M)
files={str(p.relative_to(out)):sha(p) for p in sorted(generated.rglob('*')) if p.is_file()} if generated.is_dir() else {}
gtxt=(out/'gnu-time.txt').read_text(errors='replace') if (out/'gnu-time.txt').is_file() else ''
def metric(pattern,cast=str):
 m=re.search(pattern,gtxt,re.M); return cast(m.group(1).strip()) if m else None
binding_gate=all(len(root_rows[str(i)])==1 for i in roots)
translation={'translator_exit_status':run.returncode,'generated_dir_exists':generated.is_dir(),'translation_json_exists':manifest.is_file(),'manifest_function_entries':len(funcs),'manifest_root_def_id_matches':{k:len(v) for k,v in root_rows.items()},'manifest_root_rows':root_rows,'external_template_axiom_names':external,'generated_file_sha256':files,'warning_lines':[x for x in (out/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in x]}
(out/'translation-result.json').write_text(json.dumps(translation,indent=2))
result={'translator_exit_status':run.returncode,'input_sha256':sha(source),'expected_projection_sha256':facts['expected_projection_sha256'],'binary_sha256':sha(binary),'source_revision':facts['source_revision'],'projection_source_revision':facts['projection_source_revision'],'namespace':facts['namespace'],'required_native_roots':roots,'translation':translation,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'),'peak_rss_kib':metric(r'Maximum resident set size \(kbytes\):\s*(\d+)',int),'swap_count':metric(r'Swaps:\s*(\d+)',int),'gnu_time_exit_status':metric(r'Exit status:\s*(\d+)',int),'cgroup_before':before,'cgroup_after':after,'meminfo_after':{k:v for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},'scope':'Focused translation only; no Lean compile, template fill, execution equivalence, or source/security claim.','manifest_binding_gate_passed':binding_gate}
(out/'result.json').write_text(json.dumps(result,indent=2))
print(json.dumps({'translator_exit_status':run.returncode,'wall_time':result['wall_time'],'peak_rss_kib':result['peak_rss_kib'],'swap_count':result['swap_count'],'manifest_root_matches':translation['manifest_root_def_id_matches'],'manifest_binding_gate_passed':binding_gate,'generated_files':len(files)}))
sys.exit(run.returncode if run.returncode else (0 if binding_gate else 3))
