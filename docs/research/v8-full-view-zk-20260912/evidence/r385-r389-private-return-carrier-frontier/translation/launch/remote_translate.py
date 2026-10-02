import pathlib,hashlib,subprocess,json,re
root=pathlib.Path("/home/dombarker/project-offloads/aspis-r389-private-batch-translation-20261002-a");assert not root.exists(),f'output root exists: {root}';root.mkdir()
source=pathlib.Path("/home/dombarker/project-offloads/aspis-r327-private-batch-source-try-fold-20261002-a/R327PrivateBatchSourceTryFold.llbc");binary=pathlib.Path("/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a/aeneas-r385-private-return-carrier-v2-candidate")
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source_sha=sha(source);binary_sha=sha(binary)
assert source_sha=="9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442",source_sha
assert binary_sha=="f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5",binary_sha
raw=json.loads(source.read_text());assert raw["has_errors"] is False
tr=raw["translated"];assert tr["options"]["start_from"]==["crate::circle_norm::joined_inverse::line_norm::r110_norm::batch"]
funcs=tr["fun_decls"];types=tr["type_decls"]
assert len(funcs)==54 and sum(x is not None for x in funcs)==53
assert len(types)==29
options=[x for x in types if isinstance(x,dict) and x["item_meta"].get("lang_item")=="Option"]
assert [x["def_id"] for x in options]==[9,12,13]
assert all([v["name"] for v in x["kind"]["Enum"]]==["None","Some"] for x in options)
root_fun=next(x for x in funcs if isinstance(x,dict) and x.get("def_id")==0)
assert root_fun["item_meta"]["is_local"] is True and root_fun.get("body") not in (None,"Opaque")
root_group_index=next(i for i,x in enumerate(tr["ordered_decls"]) if x=={"Fun":{"NonRec":0}})
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
previous=subprocess.check_output(['systemctl','show','aspisr385.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
active=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
containers=subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)
reservation={'meminfo_before':mem,'R385_slice_before':previous,'active_user_services':active,'active_docker_containers':containers,'memory_available_kib':int(mem['MemAvailable'].split()[0]),'new_scope_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'source_sha256':source_sha,'binary_sha256':binary_sha,'R327_source_revision':'d4bf07b08443136de0a11fc1fd932bd604586c2e','translation_launch_revision':'0910b78908f2bc7194da93514d20831dea1f9940'}
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr389.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['R389_slice_before']=subprocess.check_output(['systemctl','show','aspisr389.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR389PrivateBatch','-dest',str(root/'generated'),'-subdir','AspisR389PrivateBatch','-split-files','-emit-json',str(source)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':source_sha,'source_revision':"d4bf07b08443136de0a11fc1fd932bd604586c2e",'translation_launch_revision':"0910b78908f2bc7194da93514d20831dea1f9940",'binary_sha256':binary_sha,'namespace':'AspisR389PrivateBatch','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'input_preflight':{'has_errors':False,'function_rows':54,'nonnull_function_declarations':53,'type_declarations':29,'option_def_ids':[9,12,13],'assert_variant_key_occurrences_in_json':1},'source_gate':{'root_id':0,'root_rust_name':'aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch','root_group_index':root_group_index,'root_group':{'Fun':{'NonRec':0}},'root_local':True,'root_body_present':True}},indent=2))
with (root/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text());print('TRANSLATE_EXIT',r.returncode)
gen=root/'generated';manifest=gen/'translation.json';functions=[];root_entries=[];root_files=[];root_line=None;root_entry=None
if manifest.is_file():
 md=json.loads(manifest.read_text());functions=md.get('functions',[])
 root_entries=[f for f in functions if f.get('rust_name')=='aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch' and f.get('lean_name')=='AspisR389PrivateBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch']
 if len(root_entries)==1:
  root_entry=root_entries[0];lp=gen/root_entry['lean_file']
  if lp.is_file():
   lines=lp.read_text(errors='replace').splitlines();needle='def circle_norm.joined_inverse.line_norm.r110_norm.batch'
   matches=[i for i,line in enumerate(lines,1) if line==needle]
   if len(matches)==1:root_line=matches[0];root_files=[str(lp.relative_to(gen))]
templates={'functions':gen/'AspisR389PrivateBatch'/'FunsExternal_Template.lean','types':gen/'AspisR389PrivateBatch'/'TypesExternal_Template.lean'}
template_holes={k:(re.findall(r'^axiom\s+([^\s(]+)',v.read_text(errors='replace'),re.M) if v.is_file() else []) for k,v in templates.items()}
warnings=[line for line in (root/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in line]
generated_hashes={str(v.relative_to(root)):hashlib.sha256(v.read_bytes()).hexdigest() for v in sorted(gen.rglob('*')) if v.is_file()} if gen.is_dir() else {}
result={'translator_exit_status':r.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'function_manifest_entries':len(functions),'required_batch_root_manifest_matches':len(root_entries),'required_batch_root_entry':root_entry,'required_batch_root_lean_files':root_files,'required_batch_root_lean_definition_line':root_line,'root_in_lean_source':root_line is not None,'external_template_axiom_holes':template_holes,'translator_warnings':warnings,'generated_file_sha256':generated_hashes,'input_declaration_inventory':{'function_rows':len(funcs),'nonnull_function_declarations':sum(x is not None for x in funcs),'type_declarations':len(types),'option_instances':len(options),'assert_variant_key_occurrences_in_json':1}}
(root/'translation-result.json').write_text(json.dumps(result,indent=2))
after={'R389_slice_after':subprocess.check_output(['systemctl','show','aspisr389.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True),'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
(root/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'root_emission':result,'source_sha256':source_sha,'binary_sha256':binary_sha,'R327_source_revision':'d4bf07b08443136de0a11fc1fd932bd604586c2e','translation_launch_revision':'0910b78908f2bc7194da93514d20831dea1f9940','scope':'Translation inventory only; no external template was filled or Lean compiled.'},indent=2))
raise SystemExit(r.returncode)
