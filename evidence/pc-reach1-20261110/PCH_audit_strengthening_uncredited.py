"""Independent PCH audit facets; no compiler, proof, cache or shared-source mutation."""
import pathlib,json,lzma,hashlib,sys,re,collections,shutil,subprocess
B=pathlib.Path(__file__).resolve().parent;a,mode=sys.argv[1:];I=json.loads(lzma.decompress((B/'PCH_GRAPH_INPUT.json.xz').read_bytes()));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert shutil.disk_usage(B).free>=40_000_000_000
out=dict(attempt=a,mode=mode,print_axioms='N/A: no theorem',source_revisions=I['authority']['required'],validator_source_sha256=sha(B/'PCH_VALIDATOR.py'))
if mode=='spans':
 reports=[]
 for attempt in ['PCH_B005','PCH_B006']:
  d=json.loads((B/(attempt+'_DUMP.json')).read_text());assert d['exit_status']==0 and d['same_codegen_symbols'];p=B/(attempt+'_MIR_DUMP.json.xz');data=json.loads(lzma.decompress(p.read_bytes()));assert len(data)==d['dump_files']
  # Retain exactly which fresh diagnostic templates mention a source position within each row.
  index=collections.defaultdict(set)
  for name,text in data.items():
   for path,line in re.findall(r'((?:programs|crates)/[^\s:]+\.rs):(\d+):',text):index[(path,int(line))].add(name)
  candidates=[]
  for r in I['inventory']['rows']:
   if not r['genuinely_new']:continue
   hits=set()
   for line in range(r['source_lines'][0],r['source_lines'][1]+1):hits.update(index.get((r['source_file'],line),set()))
   candidates.append(dict(row=r['id'],source_file=r['source_file'],source_lines=r['source_lines'],diagnostic_templates=sorted(hits),conclusion='SPAN_CENSUS_ONLY; no resolved generic-instance call association'))
  reports.append(dict(attempt=attempt,template_count=len(data),dump_sha256=d['dump_sha256'],same_codegen_symbols=True,rows=candidates))
 out.update(reports=reports,changes_to_verdicts=0,reason='Source-span ownership improves the census but does not instantiate generic caller/callee type substitutions or the external handler graph.')
elif mode=='roots':
 source=(B/'src/programs/aspis-pool/src/processor.rs').read_text();features=set(json.loads((B/'PCH_B003_BUILD.json').read_text())['compiler_features']['aspis_pool']);features={s[len('feature="'):-1] for s in features}
 specs=[('AS8I','pair-forest-account-evidence','process_pair_forest_initialize_with_runtime_v1'),('AS8C','pair-forest-account-evidence','process_pair_forest_checkpoint_with_runtime_v1'),('AS8D','pair-forest-account-evidence','process_pair_forest_deposit_with_runtime_v1'),('ASQ8','pair-forest-account-evidence','process_pair_forest_terminal_v1'),('ASF8','pair-forest-full-asf8-audit','process_pair_forest_terminal_full_asf8_v1'),('ASJP','pair-afterstate-evidence','process_pair_private_transfer_with_verifier_v1'),('ASJW','pair-afterstate-evidence','process_pair_withdrawal_with_verifier_v1')]
 out['dispatch']=[dict(tag=tag,feature=feat,compiled=feat in features,callee=fn,source_line=next(i for i,l in enumerate(source.splitlines(),1) if fn+'(' in l),root='processor::process_instruction (already a graph root)',exclusion_claim=False) for tag,feat,fn in specs]
 g=json.loads(lzma.decompress((B/'PCH_GRAPH.json.xz').read_bytes()));out['graph_roots']=g['roots'];out['features']=sorted(features)
 assert {r['tag'] for r in out['dispatch'] if r['compiled']}=={'AS8I','AS8C','AS8D','ASQ8'}
 out['handler_scope']='entrypoint and custom_panic resolved in project codegen; abort/global allocator boundaries retained unresolved under c-g(7), never omitted'
 out['cfg_disabled_rows_excluded']=0
elif mode=='features':
 b=json.loads((B/'PCH_B003_BUILD.json').read_text());checks=[]
 for p,h in b['source_pins'].items():checks.append(dict(path=p,matches=sha(B/'src'/p)==h,sha256=h))
 assert all(c['matches'] for c in checks)
 assert sha(B/'src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 out.update(source_checks=checks,compiler_features=b['compiler_features'],resolved_packages=b['resolved_packages'],resolved_packages_provenance='retained exact frozen-build cargo metadata; direct rustc reproduces exact compiler cfg and ELF, no new resolution was run',toolchain=dict(path=b['command'][0],sha256=sha(pathlib.Path(b['command'][0]))),core_tables=json.loads((B/'PCH_B002_DEPENDENCIES.json').read_text())['build_inputs'],native_mir_used_for_exclusion=False)
elif mode=='extra-controls':
 import PCH_VALIDATOR as V
 g=V.load_graph();v=json.loads((B/'PCH_VERDICTS.json').read_text());results=[]
 # Distinct integrity shapes not covered by the five mandatory edge controls.
 for name in ['missing_abort_root','deleted_unknown_target','forged_witness','forged_exclusion_flags']:
  if name=='missing_abort_root':old=g['roots'];g['roots']=[r for r in old if r['instance']!='runtime-root:abort']
  elif name=='deleted_unknown_target':old=g['edges'];removed=next(e for e in old if e['kind']=='UNRESOLVED_UNIVERSAL_TARGET');g['edges']=[e for e in old if e['id']!=removed['id']];g['counts']['edges']=len(g['edges'])
  elif name=='forged_witness':old=v['rows'][0]['unresolved_witness'];v['rows'][0]['unresolved_witness']=[0]
  else:
   old=v['rows'][0];v['rows'][0]=dict(old,verdict='EXCLUDED-CANDIDATE',codegen_cross_check=dict(absence_established=True),caller_MIR_instances_resolved=True,unresolved_witness=[],resolved_codegen_witness=None)
  try:V.validate(g,v);rejected=False;reason=None
  except (AssertionError,KeyError,IndexError) as e:rejected=True;reason=str(e)
  assert rejected,name;results.append(dict(control=name,rejected=True,reason=reason))
  if name=='missing_abort_root':g['roots']=old
  elif name=='deleted_unknown_target':g['edges']=old;g['counts']['edges']=len(old)
  elif name=='forged_witness':v['rows'][0]['unresolved_witness']=old
  else:v['rows'][0]=old
 for control in ['planted_POOL_246','deleted_real_call','deleted_fn_pointer','deleted_vtable','missing_codegen_check']:
  r=subprocess.run([sys.executable,str(B/'PCH_VALIDATOR.py'),a+'_'+control,control],capture_output=True,text=True)
  assert r.returncode==0,(control,r.stdout,r.stderr)
  results.append(json.loads((B/(a+'_'+control+'_VALIDATION.json')).read_text()))
 out['controls']=results
elif mode=='accounting':
 v=json.loads((B/'PCH_VERDICTS.json').read_text());assert len(v['rows'])==278
 closed=[r for r in v['rows'] if r['inherited_status']=='CLOSED'];opened=[r for r in v['rows'] if r['inherited_status']!='CLOSED'];assert len(closed)==39 and len(opened)==239
 tests=[json.loads((B/('PCH_A'+str(n).zfill(3)+'_VALIDATION.json')).read_text()) for n in range(10,15)];assert all(t['matched'] and not t['validator_accepted'] for t in tests)
 out.update(closed=39,excluded=0,open=239,open_by_class=dict(collections.Counter(r['class_'] for r in opened)),proven_reachable_open_by_class={c:0 for c in 'ABCD'},unresolved=278,validation=tests,ledger_changes=[],assumptions_discharged=[],new_trust=[],target_established=False)
elif mode=='final':
 import PCH_VALIDATOR as V
 g=V.load_graph();v=json.loads((B/'PCH_VERDICTS.json').read_text());assert V.validate(g,v)
 out.update(validator_exit_status=0,all_rows_retained=len(v['rows']),closed_changes=0,exclusions=0,graph_sha256=sha(B/'PCH_GRAPH.json.xz'),artifact_checks={})
 for attempt in ['PCH_B005','PCH_B006']:
  d=json.loads((B/(attempt+'_DUMP.json')).read_text());assert d['exit_status']==0 and d['same_codegen_symbols'];out['artifact_checks'][attempt]=d
 assert out['artifact_checks']['PCH_B006']['elf_sha256']=='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'
else:raise RuntimeError(mode)
(B/(a+'_AUDIT.json')).write_text(json.dumps(out,indent=1)+'\n');print('PCH audit '+mode+': PASS')
