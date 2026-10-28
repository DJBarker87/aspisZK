import pathlib,json,subprocess,hashlib,tomllib
E=pathlib.Path(__file__).parent
checks={}
# Directly exercise the AST selector, including the overlapping-attribute removal shape.
ns={'__file__':str(E/'NCS_bodies.py')};code=(E/'NCS_bodies.py').read_text().split('paths=subprocess.check_output')[0];exec(compile(code,str(E/'NCS_bodies.py'),'exec'),ns)
src=b'fn f(){ #[cfg(not(feature="x"))] #[cfg(feature="y")] {old();} #[cfg(feature="x")] {new();} let z=cfg!(feature="x"); }'
tree=ns['P'].parse(src);fn=next(n for n in ns['walk'](tree.root_node)if n.type=='function_item');blk=fn.child_by_field_name('body')
selected,unknown,_,raw=ns['select'](blk,src,{'x'})
assert b'old'not in raw and b'new()'in raw and b'true'in raw and b'#[cfg'not in raw and not unknown
checks['cfg_multiple_attributes_and_cfg_macro']=True
r=json.load(open(E/'NCS_RESULTS.json'));rows=r['rows'];assert len(rows)==len({x['id']for x in rows})==192
assert sum(x['packet']=='P6'for x in rows)==13
assert all(x['roots']and x['reached_hashes']for x in rows)
assert all(x['cone_original_sha256']==x['cone_deployed_sha256']for x in rows)
assert all(x['positive_receipts']and not x['missing_exact_harness_sources']for x in rows if x['classification']=='SAME BODIES'and x['profile']!='P3')
assert all(x['missing_exact_harness_sources']for x in rows if x['classification']=='UNDETERMINED')
checks['unique_rows_13_leaves_complete_pair_hashes_and_unknown_reasons']=True
b=json.load(open(E/'NCS_BODY_HASHES.json'));assert not b['parse_errors'];assert len(b['bodies'])==9069
assert len(b['changed_library_bodies'])==9
checks['all_frozen_source_files_parse_and_changes_retained']=True
# Class-based comparison must be supported by every captured historical local feature graph.
canonical={j['label']:{n['name']:n['features']for n in j['nodes']if n['name'].startswith('aspis-')}for l in (E/'NCS_I002-stdout.log').read_text().splitlines()if(j:=json.loads(l))}
for file in ['NCS_I003-stdout.log','NCS_I005-stdout.log']:
 for line in (E/file).read_text().splitlines():
  j=json.loads(line);assert j['exists']and j['exit']==0
  local={n['name']:n['features']for n in j['nodes']if n['name'].startswith('aspis-')}
  assert local in canonical.values(),(j['manifest'],local)
checks['all_33_historical_graphs_match_recorded_classes']=True
lf=canonical['library-deployed']['aspis-statement'];assert len(set(lf)-{'r0','pool-v1-kernel'})==12
checks['exactly_12_deployed_statement_optimization_features']=True
attempts=[json.loads(l)for l in (E/'NCS_ATTEMPTS.jsonl').read_text().splitlines()];assert len(attempts)==6
for a in attempts:
 assert a['exit_status']==0 and a['admission_allowed']is True and a['admission_exit']==0 and a['swaps']==0
 cmd=a['scope_command'];assert all(s in cmd for s in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert not any(s in ' '.join(cmd)for s in ['cargo-kani','lake env lean','kani-driver'])
checks['six_serial_admitted_capped_inspections_zero_provers']=True
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024]
checks['no_artifact_over_20_MiB']=True
changed=subprocess.check_output(['git','diff','--name-only','9738b05e2a']).decode().splitlines()
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard']).decode().splitlines()
evidence_prefix=str(E.resolve().relative_to(pathlib.Path.cwd()))+'/'
assert all(p.startswith(evidence_prefix)for p in changed+new)
checks['only_task_evidence_changed']=True
subprocess.run(['git','diff','--check'],check=True)
checks['git_diff_check']=True
inputs=['NCS_PARITY_AUDIT.md','NCS_SUSPENDED.json','NCS_RESULTS.json','NCS_BODY_HASHES.json','NCS_HARNESS_AUDIT.json','NCS_ATTEMPTS.jsonl']
result=dict(exit_status=0,checks=checks,summary=r['summary'],revision_before_final_commit=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),artifact_sha256={f:hashlib.sha256((E/f).read_bytes()).hexdigest()for f in inputs},no_new_axioms='No Lean invoked',runtime_validation='Reused historical results, no Kani replay')
(E/'NCS_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
