import datetime,hashlib,json,pathlib,subprocess,sys,re,os
facts=json.loads(sys.argv[1]);src=pathlib.Path(facts['candidate_remote']);base=pathlib.Path(facts['baseline_remote']);binary=pathlib.Path(facts['binary']);out=pathlib.Path(facts['remote_output']);work=pathlib.Path(facts['workroot'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not out.exists(),f'fresh output path already exists: {out}'
assert sha(src)==facts['candidate_sha'],sha(src);assert sha(base)==facts['baseline_sha'],sha(base);assert sha(binary)==facts['binary_sha'],sha(binary)
for p,expected in ((src,facts['candidate_sha']),(base,facts['baseline_sha'])):
 d=json.loads(p.read_text());assert d.get('has_errors') is False;tr=d['translated'];assert tr['options']['start_from']==['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch'];assert len(tr['ordered_decls'])==161
# Aggregate gate: preserve current host evidence and require spare reserve before entering the capped scope.
mem={k:v for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
avail=int(mem['MemAvailable'].split()[0])*1024;cap=7*1024**3;reserve=24*1024**3;assert avail-cap>=reserve,{'meminfo':mem,'cap':cap,'reserve':reserve}
heavy=[]
for p in pathlib.Path('/proc').iterdir():
 if p.name.isdigit():
  try:
   comm=(p/'comm').read_text().strip()
   if comm in ('cargo','rustc','rustc_driver','charon','aeneas','lean','lean4'):heavy.append({'pid':p.name,'comm':comm})
  except (OSError,FileNotFoundError):pass
assert not heavy,heavy
out.mkdir(parents=True)
pre={'candidate_sha256':sha(src),'baseline_sha256':sha(base),'binary_sha256':sha(binary),'source_revision':'3f22e765d32b16d016f4ff603d599ea72838c37a','translation_launch_revision':'a3fe5df6b53caa52322339906642de5064fc2bbb','meminfo_before':mem,'candidate_memory_max_bytes':cap,'reserve_bytes':reserve,'heavy_processes':heavy,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}}
(out/'host-reservation-before.json').write_text(json.dumps(pre,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR424GenericBatch','-dest',str(out/'generated'),'-subdir','AspisR424GenericBatch','-split-files','-emit-json',str(src)]
(out/'translate-command.json').write_text(json.dumps({'command':cmd,'candidate_sha256':sha(src),'baseline_sha256':sha(base),'binary_sha256':sha(binary),'source_revision':'3f22e765d32b16d016f4ff603d599ea72838c37a','translation_launch_revision':'a3fe5df6b53caa52322339906642de5064fc2bbb','namespace':'AspisR424GenericBatch','flags':['-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR424GenericBatch','-dest','<fresh>/generated','-subdir','AspisR424GenericBatch','-split-files','-emit-json']},indent=2))
with (out/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
gen=out/'generated';manifest=gen/'translation.json';md=json.loads(manifest.read_text()) if manifest.is_file() else {};functions=md.get('functions',[])
rootrows=[f for f in functions if f.get('rust_name')=='aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch'];warnings=[x for x in (out/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in x]
holes={}
for fname in ('FunsExternal_Template.lean','TypesExternal_Template.lean'):
 p=gen/'AspisR424GenericBatch'/fname
 holes[fname]=re.findall(r'^axiom\s+([^\s(]+)',p.read_text(errors='replace'),re.M) if p.is_file() else []
files={str(p.relative_to(out)):sha(p) for p in sorted(gen.rglob('*')) if p.is_file()} if gen.is_dir() else {}
result={'translator_exit_status':r.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'manifest_function_entries':len(functions),'batch_root_matches':len(rootrows),'batch_root_entry':rootrows[0] if len(rootrows)==1 else None,'external_template_axiom_holes':holes,'warnings':warnings,'generated_file_sha256':files,'input_has_errors':False,'input_ordered_decls':161,'source_gate_boundary':'R419 candidate is the only input; root body was inventoried before launch and expected-delta review was required locally.'}
(out/'translation-result.json').write_text(json.dumps(result,indent=2))
after={'meminfo_after':{k:v for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(out/'host-reservation-after.json').write_text(json.dumps(after,indent=2));(out/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'candidate_sha256':sha(src),'baseline_sha256':sha(base),'binary_sha256':sha(binary),'candidate_transform_source_revision':'3f22e765d32b16d016f4ff603d599ea72838c37a','translation_launch_revision':'a3fe5df6b53caa52322339906642de5064fc2bbb','translation_result':result,'scope':'Translation inventory only; no Lean compile, template fill, proof, or source claim.'},indent=2))
print((out/'translate.log').read_text()[-12000:]);print('R424_TRANSLATE_EXIT',r.returncode);raise SystemExit(r.returncode)
