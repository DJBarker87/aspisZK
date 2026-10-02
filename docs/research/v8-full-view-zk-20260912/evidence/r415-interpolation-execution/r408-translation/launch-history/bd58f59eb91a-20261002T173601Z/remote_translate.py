import pathlib,hashlib,subprocess,json,re,os
src=pathlib.Path("/home/dombarker/project-offloads/aspis-r403-interpolate-three-constant-limb-20261002-a/R403InterpolateThreeConstantLimb.llbc");binary=pathlib.Path("/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a/aeneas-r385-private-return-carrier-v2-candidate");root=pathlib.Path("/home/dombarker/project-offloads/aspis-r408-interpolate-three-limb-translation-20261002-b")
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not root.exists(),f'output root exists: {root}'
assert sha(src)=="6bfbbddbcef03a061ab564b40ccea4f7408d28a6a01010ca16229d349c428efa",sha(src)
assert sha(binary)=="f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5",sha(binary)
raw=json.loads(src.read_text());assert raw.get('has_errors') is False
tr=raw['translated'];rootfn=next(x for x in tr['fun_decls'] if x and x.get('def_id')==0)
assert tr['options']['start_from']==["aspis_statement::state_only_poseidon::interpolate_three_constant_limb"]
assert tr['options']['include']==['aspis_core::field',"aspis_statement::state_only_poseidon::interpolate_three_constant_limb"]
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
pre={'source_sha256':sha(src),'source_bytes':src.stat().st_size,'binary_sha256':sha(binary),'binary_size':binary.stat().st_size,'source_campaign_revision':'d473563212029be91ea1032bfd2ef70ee6d68b73','translation_launch_revision':'bd58f59eb91a222a78753e9bc1f88890f3e7c4fd','meminfo_before':mem_before,'running_user_services':active,'active_processes_at_gate':procs,'active_docker_containers':containers,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}}
pre['slice_before']=subprocess.check_output(['systemctl','show','aspisr408b.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(pre,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR403InterpolateThreeLimb','-dest',str(root/'generated'),'-subdir','AspisR403InterpolateThreeLimb','-split-files','-emit-json',str(src)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':sha(src),'source_campaign_revision':'d473563212029be91ea1032bfd2ef70ee6d68b73','translation_launch_revision':'bd58f59eb91a222a78753e9bc1f88890f3e7c4fd','binary_sha256':sha(binary),'namespace':'AspisR403InterpolateThreeLimb','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'input_inventory':{'types':1,'funs':5,'globals':1,'trait_decls':1,'trait_impls':1,'ordered_decls':7,'root_fun_id':0,'root_name':'aspis_statement::state_only_poseidon::interpolate_three_constant_limb','root_body':'Structured','opaque_fun_id_1_calls':6}},indent=2))
with (root/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
manifest=root/'generated'/'translation.json';gen=root/'generated';warnings=[];templates={};functions=[];types=[];root_matches=[];from_strings=[]
if manifest.is_file():
 md=json.loads(manifest.read_text());functions=md.get('functions',[]);types=md.get('types',[])
 for x in functions:
  if 'aspis_statement::state_only_poseidon::interpolate_three_constant_limb' in str(x) or 'interpolate_three_constant_limb' in str(x):root_matches.append(x)
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
(root/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'source_sha256':sha(src),'binary_sha256':sha(binary),'source_campaign_revision':'d473563212029be91ea1032bfd2ef70ee6d68b73','translation_launch_revision':'bd58f59eb91a222a78753e9bc1f88890f3e7c4fd','result':result,'scope':'Translation inventory only; no generated Lean compile, template filling, or proof.'},indent=2))
print((root/'translate.log').read_text()[-10000:]);print('R408_TRANSLATE_EXIT',r.returncode)
raise SystemExit(r.returncode)
