#!/usr/bin/env python3
"""Authorized unchanged-input R398 Aeneas translation; source is never rewritten."""
import argparse,datetime,hashlib,json,pathlib,re,shlex,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=HERE.parents[1]
HOST='dombarker@100.108.41.90'
SSH=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
LOCAL_INPUT=WORKTREE/'.r21-scratch/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'
SOURCE='/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc'
BINARY='/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a/aeneas-r385-private-return-carrier-v2-candidate'
WORKROOT='/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
OUTROOT='/home/dombarker/project-offloads/aspis-r398-generic-batch-translation-20261002-a'
INPUT_SHA='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
BINARY_SHA='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
SOURCE_REV='13617a70553ed3c43cee312acba2407b29a7052d'
ROOT_RUST='aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch'
ROOT_LEAN='AspisR398GenericBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch'
NAMESPACE='AspisR398GenericBatch'
CAPS={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def method_name(row):
 parts=[]
 for x in row.get('item_meta',{}).get('name') or []:
  if 'Ident' in x:parts.append(x['Ident'][0])
  elif 'Impl' in x:parts.append('{impl}')
  elif 'Instantiated' in x:parts.append('{instantiated}')
  else:parts.append('{other}')
 return '::'.join(parts)
def local_gate():
 assert sha(LOCAL_INPUT)==INPUT_SHA
 raw=json.loads(LOCAL_INPUT.read_text());tr=raw['translated'];assert raw['has_errors'] is False
 assert tr['options']['start_from']==['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
 rows=[r for r in tr['fun_decls'] if isinstance(r,dict) and method_name(r)== 'core::iter::traits::iterator::Iterator::try_fold' and r.get('item_meta',{}).get('span',{}).get('data',{}).get('beg')=={'line':2486,'col':4} and r.get('item_meta',{}).get('span',{}).get('data',{}).get('end')=={'line':2490,'col':35}]
 assert len(rows)==1 and rows[0].get('body') not in (None,'Opaque')
 return {'input_sha256':INPUT_SHA,'input_bytes':LOCAL_INPUT.stat().st_size,'has_errors':False,'function_rows':len(tr['fun_decls']),'nonnull_functions':sum(isinstance(x,dict) for x in tr['fun_decls']),'type_rows':len(tr['type_decls']),'global_rows':len(tr['global_decls']),'trait_rows':len(tr['trait_decls']),'trait_impl_rows':len(tr['trait_impls']),'start_from':tr['options']['start_from'],'selected_try_fold':{'def_id':rows[0]['def_id'],'qualified_name':method_name(rows[0]),'span':rows[0]['item_meta']['span'],'body_present':True},'unmodified_source':True}
REMOTE=r'''import pathlib,hashlib,subprocess,json,re,os
source=pathlib.Path("@SOURCE@");binary=pathlib.Path("@BINARY@");root=pathlib.Path("@OUTROOT@");work=pathlib.Path("@WORKROOT@");
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not root.exists(),f'fresh output root already exists: {root}'
source_sha=sha(source);binary_sha=sha(binary);assert source_sha=="@INPUT_SHA@",source_sha;assert binary_sha=="@BINARY_SHA@",binary_sha
raw=json.loads(source.read_text());assert raw['has_errors'] is False
tr=raw['translated'];assert tr['options']['start_from']==['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
assert len(tr['ordered_decls'])==161
funcs=tr['fun_decls'];types=tr['type_decls'];globals_=tr['global_decls'];traits=tr['trait_decls'];impls=tr['trait_impls']
assert sum(isinstance(x,dict) for x in funcs)==sum(isinstance(x,dict) for x in funcs)
def name(r):
 out=[]
 for x in r.get('item_meta',{}).get('name') or []:
  if 'Ident' in x:out.append(x['Ident'][0])
  elif 'Impl' in x:out.append('{impl}')
  elif 'Instantiated' in x:out.append('{instantiated}')
 return '::'.join(out)
selected=[]
for x in funcs:
 if not isinstance(x,dict) or name(x)!='core::iter::traits::iterator::Iterator::try_fold':continue
 sp=x.get('item_meta',{}).get('span',{}).get('data',{})
 if (sp.get('beg',{}).get('line'),sp.get('beg',{}).get('col'),sp.get('end',{}).get('line'),sp.get('end',{}).get('col'))==(2486,4,2490,35):selected.append(x)
assert len(selected)==1 and selected[0].get('body') not in (None,'Opaque')
root.mkdir()
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
memtotal=int(mem['MemTotal'].split()[0])*1024;available=int(mem['MemAvailable'].split()[0])*1024
cap=7*1024**3;reserve=24*1024**3;limit=min(40*1024**3,memtotal-16*1024**3)
assert available-cap>=reserve and cap<=limit,{'mem':mem,'candidate':cap,'reserve':reserve,'limit':limit}
units=subprocess.check_output(['systemctl','list-units','--all','--type=slice','--no-legend'],text=True).splitlines();sliceinfo=[];activecaps=0
for line in units:
 n=line.split()[0]
 if not n.startswith('aspis'):continue
 props=subprocess.check_output(['systemctl','show',n,'-p','ControlGroup','-p','MemoryMax','-p','MemoryCurrent'],text=True);v=dict(z.split('=',1) for z in props.splitlines() if '=' in z)
 cg=pathlib.Path('/sys/fs/cgroup')/v.get('ControlGroup','').lstrip('/');pids=[]
 if cg.exists():
  for f in cg.rglob('cgroup.procs'):
   try:pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
   except OSError:pass
 maxv=int(v.get('MemoryMax','0')) if v.get('MemoryMax','0').isdigit() else 0
 if pids:activecaps+=maxv
 sliceinfo.append({'unit':n,'control_group':v.get('ControlGroup'),'memory_max_bytes':maxv,'memory_current_bytes':int(v.get('MemoryCurrent','0') or 0),'pids':pids})
assert not any(x['pids'] for x in sliceinfo),sliceinfo
procs=subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines();heavy=[q.strip() for q in procs if len(q.split())>1 and q.split()[1] in ('cargo','rustc','rustc_driver','charon','aeneas','lean','lean4')]
assert not heavy,heavy
assert activecaps+cap<=limit,{'active_caps':activecaps,'candidate':cap,'limit':limit}
reservation={'meminfo_before':mem,'available_after_candidate_cap_bytes':available-cap,'required_post_candidate_reserve_bytes':reserve,'candidate_memory_max_bytes':cap,'active_aspis_slice_caps_bytes':activecaps,'safe_cap_sum_bytes':limit,'aspis_slices':sliceinfo,'heavy_processes':heavy,'source_sha256':source_sha,'binary_sha256':binary_sha,'source_revision':'@SOURCE_REV@','launch_revision':'@LAUNCH_REV@'}
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr398.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['scope_before']=subprocess.check_output(['systemctl','show','aspisr398.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR398GenericBatch','-dest',str(root/'generated'),'-subdir','AspisR398GenericBatch','-split-files','-emit-json',str(source)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':source_sha,'binary_sha256':binary_sha,'source_revision':'@SOURCE_REV@','launch_revision':'@LAUNCH_REV@','namespace':'AspisR398GenericBatch','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'input_declaration_counts':{'ordered_decls':len(tr['ordered_decls']),'functions':len(funcs),'nonnull_functions':sum(isinstance(x,dict) for x in funcs),'types':len(types),'globals':len(globals_),'traits':len(traits),'trait_impls':len(impls)},'selected_try_fold':{'def_id':selected[0]['def_id'],'source_span':selected[0]['item_meta']['span'],'body_present':True},'scope_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}},indent=2))
with (root/'translate.log').open('w') as f:run=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text());print('R398_TRANSLATE_EXIT',run.returncode)
gen=root/'generated';manifest=gen/'translation.json';md=json.loads(manifest.read_text()) if manifest.is_file() else {};functions=md.get('functions',[])
rootrows=[f for f in functions if f.get('rust_name')=='@ROOT_RUST@']
rootfile=None;rootline=None
if len(rootrows)==1:
 rootfile=gen/rootrows[0]['lean_file']; lines=rootfile.read_text(errors='replace').splitlines() if rootfile.is_file() else []; candidates=['def circle_norm.joined_inverse.line_norm.r110_norm.batch','def AspisR398GenericBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch']; hits=[(i,l) for i,l in enumerate(lines,1) if l.strip() in candidates]
 if len(hits)==1:rootline=hits[0][0]
templates={k:gen/'AspisR398GenericBatch'/n for k,n in [('functions','FunsExternal_Template.lean'),('types','TypesExternal_Template.lean')]}
holes={k:(re.findall(r'^axiom\s+([^\s(]+)',p.read_text(errors='replace'),re.M) if p.is_file() else []) for k,p in templates.items()}
warnings=[x for x in (root/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in x]
files={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(gen.rglob('*')) if f.is_file()} if gen.is_dir() else {}
result={'translator_exit_status':run.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'manifest_function_entries':len(functions),'batch_root_matches':len(rootrows),'batch_root_entry':rootrows[0] if len(rootrows)==1 else None,'batch_root_lean_file':str(rootfile.relative_to(gen)) if rootfile and rootfile.is_file() else None,'batch_root_definition_line':rootline,'root_in_lean_source':rootline is not None,'external_template_axiom_holes':holes,'translator_warnings':warnings,'generated_file_sha256':files,'input_declaration_counts':{'ordered_decls':len(tr['ordered_decls']),'functions':len(funcs),'nonnull_functions':sum(isinstance(x,dict) for x in funcs),'types':len(types),'globals':len(globals_),'traits':len(traits),'trait_impls':len(impls)},'source_gate':{'hash':source_sha,'has_errors':False,'generic_try_fold_body_present':True}}
(root/'translation-result.json').write_text(json.dumps(result,indent=2))
after={'scope_after':subprocess.check_output(['systemctl','show','aspisr398.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True),'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
(root/'result.json').write_text(json.dumps({'translator_exit_status':run.returncode,'translation_result':result,'source_sha256':source_sha,'binary_sha256':binary_sha,'source_revision':'@SOURCE_REV@','launch_revision':'@LAUNCH_REV@','scope':'Translation inventory only; no templates filled and no Lean compilation.'},indent=2))
raise SystemExit(run.returncode)
'''
def replace_all(text,mapping):
 for k,v in mapping.items():text=text.replace(k,v)
 return text
parser=argparse.ArgumentParser();parser.add_argument('--launch-authorized-r398',action='store_true')
a=parser.parse_args();
assert sha(LOCAL_INPUT)==INPUT_SHA
local=local_gate()
if not a.launch_authorized_r398:
 print(json.dumps({'status':'prepared-only','input_gate':local,'binary_sha256':BINARY_SHA,'caps':CAPS,'translation_flags':['-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',NAMESPACE,'-dest','<fresh>','-subdir',NAMESPACE,'-split-files','-emit-json','<unchanged R396 LLBC>'],'launch_authorized_by_lead':True},indent=2));raise SystemExit(0)
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=WORKTREE,text=True).strip();assert len(revision)==40
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'); hist=HERE/'launch-history'/f'{revision[:12]}-{stamp}';hist.mkdir(parents=True,exist_ok=False)
mapping={'@SOURCE@':SOURCE,'@BINARY@':BINARY,'@OUTROOT@':OUTROOT,'@WORKROOT@':WORKROOT,'@INPUT_SHA@':INPUT_SHA,'@BINARY_SHA@':BINARY_SHA,'@SOURCE_REV@':SOURCE_REV,'@LAUNCH_REV@':revision,'@ROOT_RUST@':ROOT_RUST}
payload=REMOTE
for k,v in mapping.items():payload=payload.replace(k,v)
(hist/'remote_translate.py').write_text(payload)
outer=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r398-generic-batch-translation','--working-directory='+WORKROOT,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',payload]
ssh=['ssh',*SSH,HOST,shlex.join(outer)]
receipt={'launch_revision':revision,'timestamp_utc':stamp,'source_revision':SOURCE_REV,'input_sha256':INPUT_SHA,'binary_sha256':BINARY_SHA,'remote_payload_sha256':sha(hist/'remote_translate.py'),'local_gate':local,'systemd_argv':outer,'ssh_argv':ssh,'caps':CAPS,'no_input_rewrite':True,'translation_only':True}
(hist/'launch.json').write_text(json.dumps(receipt,indent=2)+'\n')
with (hist/'launch.log').open('w') as log:proc=subprocess.run(ssh,stdout=log,stderr=subprocess.STDOUT)
receipt['launcher_exit_status']=proc.returncode;(hist/'launch-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
out=HERE/'output'/f'{revision[:12]}-{stamp}';out.mkdir(parents=True,exist_ok=False)
scp=subprocess.run(['scp','-r',*SSH,HOST+':'+OUTROOT+'/.',str(out)])
receipt['scp_exit_status']=scp.returncode;(hist/'launch-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'launcher_exit_status':proc.returncode,'scp_exit_status':scp.returncode,'history':str(hist),'output':str(out)},indent=2))
raise SystemExit(proc.returncode if proc.returncode else scp.returncode)
