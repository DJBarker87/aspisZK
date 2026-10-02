#!/usr/bin/env python3
"""One authorized translation inventory of unchanged R403 LLBC with pinned R385 v2."""
import datetime, hashlib, json, pathlib, shlex, subprocess, sys

HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=HERE.parents[1]
HOST='dombarker@100.108.41.90'
SSH_OPTS=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SOURCE_LOCAL=WORKTREE/'.r21-scratch/r403-interpolate-three-constant-limb-included-extract/R403InterpolateThreeConstantLimb.llbc'
SOURCE_REMOTE='/home/dombarker/project-offloads/aspis-r403-interpolate-three-constant-limb-20261002-a/R403InterpolateThreeConstantLimb.llbc'
BINARY='/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a/aeneas-r385-private-return-carrier-v2-candidate'
REMOTE_WORKTREE='/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
REMOTE_ROOT='/home/dombarker/project-offloads/aspis-r408-interpolate-three-limb-translation-20261002-b'
SOURCE_SHA='6bfbbddbcef03a061ab564b40ccea4f7408d28a6a01010ca16229d349c428efa'
BINARY_SHA='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
EXTRACT_REV='d473563212029be91ea1032bfd2ef70ee6d68b73'
ROOT_NAME='aspis_statement::state_only_poseidon::interpolate_three_constant_limb'
NAMESPACE='AspisR403InterpolateThreeLimb'

raw=json.loads(SOURCE_LOCAL.read_text())
t=raw['translated']
assert hashlib.sha256(SOURCE_LOCAL.read_bytes()).hexdigest()==SOURCE_SHA
assert raw.get('has_errors') is False
assert t.get('options',{}).get('start_from')==[ROOT_NAME]
assert t.get('options',{}).get('include')==['aspis_core::field',ROOT_NAME]
assert (len(t['type_decls']),len(t['fun_decls']),len(t['global_decls']),len(t['trait_decls']),len(t['trait_impls']),len(t['ordered_decls']))==(1,5,1,1,1,7)
root=next(x for x in t['fun_decls'] if x and x.get('def_id')==0)
assert root['item_meta']['opacity']=='Transparent' and root['item_meta']['is_local'] is False
assert isinstance(root.get('body'),dict) and 'Structured' in root['body']
opaque=next(x for x in t['fun_decls'] if x and x.get('def_id')==1)
assert opaque.get('body')=='Opaque' and opaque['item_meta']['opacity']=='Foreign'
# Exact call counts retained as preflight facts, without interpreting the calls.
def regular_fun_counts(obj):
 counts={}
 def w(x):
  if isinstance(x,dict):
   if 'Call' in x and isinstance(x['Call'],dict):
    f=x['Call'].get('call',{}).get('func',{}).get('Regular',{}).get('kind',{}).get('Fun',{})
    if 'Regular' in f: counts[f['Regular']]=counts.get(f['Regular'],0)+1
   for v in x.values():w(v)
  elif isinstance(x,list):
   for v in x:w(v)
 w(obj);return counts
assert regular_fun_counts(root['body'])=={1:6,2:1}
local_preflight={'source_sha256':SOURCE_SHA,'source_bytes':SOURCE_LOCAL.stat().st_size,'has_errors':False,'start_from':t['options']['start_from'],'include':t['options']['include'],'counts':{'types':1,'funs':5,'globals':1,'trait_decls':1,'trait_impls':1,'ordered_decls':7},'root':{'id':0,'name':ROOT_NAME,'body':'Structured','local':False,'opacity':'Transparent'},'root_call_counts':{'Fun1':6,'Fun2':1},'Fun1_frontier':{'name':'core::convert::num::<From>::from','body':'Opaque','opacity':'Foreign'},'no_LLBC_projection_or_metadata_rewrite':True}

REMOTE_SCRIPT=r'''import pathlib,hashlib,subprocess,json,re,os
src=pathlib.Path("@SOURCE@");binary=pathlib.Path("@BINARY@");root=pathlib.Path("@ROOT@")
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not root.exists(),f'output root exists: {root}'
assert sha(src)=="@SOURCE_SHA@",sha(src)
assert sha(binary)=="@BINARY_SHA@",sha(binary)
raw=json.loads(src.read_text());assert raw.get('has_errors') is False
tr=raw['translated'];rootfn=next(x for x in tr['fun_decls'] if x and x.get('def_id')==0)
assert tr['options']['start_from']==["@ROOT_NAME@"]
assert tr['options']['include']==['aspis_core::field',"@ROOT_NAME@"]
assert (len(tr['type_decls']),len(tr['fun_decls']),len(tr['global_decls']),len(tr['trait_decls']),len(tr['trait_impls']),len(tr['ordered_decls']))==(1,5,1,1,1,7)
assert rootfn['item_meta']['opacity']=='Transparent' and rootfn['item_meta']['is_local'] is False and isinstance(rootfn.get('body'),dict) and 'Structured' in rootfn['body']
opaque=next(x for x in tr['fun_decls'] if x and x.get('def_id')==1);assert opaque.get('body')=='Opaque'
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
procs=[]
for p in pathlib.Path('/proc').iterdir():
 if p.name.isdigit():
  try:
   comm=(p/'comm').read_text().strip()
   if comm in ('cargo','rustc','charon'):procs.append({'pid':p.name,'comm':comm})
  except (FileNotFoundError,PermissionError):pass
assert not procs,procs
active=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
containers=subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)
mem_before=mem
root.mkdir()
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr408b.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
pre={'source_sha256':sha(src),'source_bytes':src.stat().st_size,'binary_sha256':sha(binary),'binary_size':binary.stat().st_size,'source_campaign_revision':'@EXTRACT_REV@','translation_launch_revision':'@LAUNCH_REV@','meminfo_before':mem_before,'running_user_services':active,'active_processes_at_gate':procs,'active_docker_containers':containers,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}}
pre['slice_before']=subprocess.check_output(['systemctl','show','aspisr408b.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(pre,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','@NAMESPACE@','-dest',str(root/'generated'),'-subdir','@NAMESPACE@','-split-files','-emit-json',str(src)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':sha(src),'source_campaign_revision':'@EXTRACT_REV@','translation_launch_revision':'@LAUNCH_REV@','binary_sha256':sha(binary),'namespace':'@NAMESPACE@','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'input_inventory':{'types':1,'funs':5,'globals':1,'trait_decls':1,'trait_impls':1,'ordered_decls':7,'root_fun_id':0,'root_name':'@ROOT_NAME@','root_body':'Structured','opaque_fun_id_1_calls':6}},indent=2))
with (root/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
manifest=root/'generated'/'translation.json';gen=root/'generated';warnings=[];templates={};functions=[];types=[];root_matches=[];from_strings=[]
if manifest.is_file():
 md=json.loads(manifest.read_text());functions=md.get('functions',[]);types=md.get('types',[])
 for x in functions:
  if '@ROOT_NAME@' in str(x) or 'interpolate_three_constant_limb' in str(x):root_matches.append(x)
 for fp in gen.rglob('*.lean'):
  text=fp.read_text(errors='replace')
  if 'FromU64U32' in text or 'From' in text and 'from' in text:from_strings.append(str(fp.relative_to(gen)))
  if fp.name=='FunsExternal_Template.lean' or 'External_Template' in fp.name:
   templates[str(fp.relative_to(gen))]=re.findall(r'^axiom\s+([^\s(]+)',text,re.M)
 warnings=[line for line in (root/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in line]
files={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.rglob('*')) if p.is_file() and p.name not in ('result.json','translation-result.json','host-reservation-after.json')}
result={'translator_exit_status':r.returncode,'source_sha256':sha(src),'binary_sha256':sha(binary),'translation_json_exists':manifest.is_file(),'function_manifest_entries':len(functions),'type_manifest_entries':len(types),'root_related_manifest_entries':root_matches,'root_related_lean_files':from_strings,'external_template_axiom_holes':templates,'warnings':warnings,'precompile_generated_file_hashes':files,'opaque_source_method_audit':'The exact LLBC has Fun1 Opaque and root Fun0 calls Fun1 six times. This result inventories translator output names/templates only; no Rust Std implementation or semantics are asserted.'}
(root/'translation-result.json').write_text(json.dumps(result,indent=2))
after={'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},'slice_after':subprocess.check_output(['systemctl','show','aspisr408b.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
(root/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'source_sha256':sha(src),'binary_sha256':sha(binary),'source_campaign_revision':'@EXTRACT_REV@','translation_launch_revision':'@LAUNCH_REV@','result':result,'scope':'Translation inventory only; no generated Lean compile, template filling, or proof.'},indent=2))
print((root/'translate.log').read_text()[-10000:]);print('R408_TRANSLATE_EXIT',r.returncode)
raise SystemExit(r.returncode)
'''
repl={'@SOURCE@':SOURCE_REMOTE,'@BINARY@':BINARY,'@ROOT@':REMOTE_ROOT,'@SOURCE_SHA@':SOURCE_SHA,'@BINARY_SHA@':BINARY_SHA,'@EXTRACT_REV@':EXTRACT_REV,'@LAUNCH_REV@':'CAPTURE_AT_LAUNCH','@ROOT_NAME@':ROOT_NAME,'@NAMESPACE@':NAMESPACE}

def payload(launch_rev):
 s=REMOTE_SCRIPT
 for k,v in repl.items():s=s.replace(k,v)
 return s.replace('CAPTURE_AT_LAUNCH',launch_rev)

launch_rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=WORKTREE,text=True).strip()
assert len(launch_rev)==40
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
history=HERE/'launch-history'/f'{launch_rev[:12]}-{stamp}';history.mkdir(parents=True,exist_ok=False)
remote_script=payload(launch_rev);(history/'remote_translate.py').write_text(remote_script)
script_sha=hashlib.sha256((history/'remote_translate.py').read_bytes()).hexdigest()
outer=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r408b-interpolate-three-limb-translation','--working-directory='+REMOTE_WORKTREE,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',remote_script]
ssh=['ssh',*SSH_OPTS,HOST,shlex.join(outer)]
receipt={'actual_translation_launch_revision':launch_rev,'R403_extraction_campaign_revision':EXTRACT_REV,'timestamp_utc':stamp,'source_sha256':SOURCE_SHA,'source_remote':SOURCE_REMOTE,'candidate_binary_sha256':BINARY_SHA,'candidate_binary_remote':BINARY,'namespace':NAMESPACE,'remote_root':REMOTE_ROOT,'remote_payload_sha256':script_sha,'local_preflight':local_preflight,'ssh_argv':ssh,'systemd_argv':outer,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'scope':'one sequential translation inventory; no Lean compile or template filling'}
(history/'launch.json').write_text(json.dumps(receipt,indent=2)+'\n')
with (history/'launch.log').open('w') as f:r=subprocess.run(ssh,stdout=f,stderr=subprocess.STDOUT)
receipt['launcher_exit_status']=r.returncode
(history/'launch-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
output=HERE/'output'/f'{launch_rev[:12]}-{stamp}';output.mkdir(parents=True,exist_ok=False)
scp=subprocess.run(['scp','-r',*SSH_OPTS,HOST+':'+REMOTE_ROOT+'/.',str(output)])
receipt['scp_exit_status']=scp.returncode
(history/'launch-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'launcher_exit_status':r.returncode,'scp_exit_status':scp.returncode,'history':str(history),'output':str(output),'remote_payload_sha256':script_sha},indent=2))
if r.returncode:raise SystemExit(r.returncode)
if scp.returncode:raise SystemExit(scp.returncode)
