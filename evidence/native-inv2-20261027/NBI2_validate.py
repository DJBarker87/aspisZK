#!/usr/bin/env python3
"""Independent, compile-free integrity checks of the delivered inventory.
Never starts a host job or changes shipped code. No theorem/semantic equivalence claim.
"""
import pathlib,json,hashlib,subprocess,time,resource,sys,platform
O=pathlib.Path(__file__).resolve().parent;R=O.parents[1]
start=time.monotonic(); D=json.load(open(O/'NBI2_INVENTORY.json'));rev=D['source_revision']
sha=lambda b:hashlib.sha256(b).hexdigest()
files={v['file']:subprocess.check_output(['git','show',rev+':'+v['file']],cwd=R) for v in D['functions']}
reachpath=R/'evidence/replay-deployed2-20261027/RPx_reachable-constants.json';C=set(json.load(open(reachpath)))
checks=[]
def check(label,cond):
 checks.append(dict(check=label,passed=bool(cond)))
 if not cond:raise AssertionError(label)
ids={v['id'] for v in D['functions']}
check('unique function IDs',len(ids)==len(D['functions']))
for v in D['functions']:
 b=files[v['file']]
 check(v['id']+' frozen file SHA256',sha(b)==v['file_sha256'])
 body=b[v['body_start_byte']:v['body_end_byte']]
 check(v['id']+' exact frozen body SHA256',sha(body)==v['body_sha256'] and body[:1]==b'{' and body[-1:]==b'}')
 check(v['id']+' frozen line anchor',b[:v['body_start_byte']].count(b'\n')+1>=v['line'] and v['end_line']>=v['line'])
 for c in v['calls']:
  check(v['id']+' resolved call targets at '+str(c['line']),all(t in ids for t in c['targets']))
  check(v['id']+' no unresolved dispatch at '+str(c['line']),c['resolution']!='unresolved native dispatch')
 for c in v['cohort_definitions']+v['model_context']:
  check(c['name']+' retained kernel membership',c['name'] in C)
  check(c['name']+' source locator exists',bool(c.get('file')) and (R/c['file']).is_file())
  check(c['name']+' source snapshot SHA256',sha((R/c['file']).read_bytes())==c['source_sha256'])
 for c in v['callee_domains']:check(v['id']+' domain edge '+c['function'],c['function'] in ids)
seen=set()
for u in D['bridge_units_bottom_up']:
 check(u['id']+' ordered callee units',all(c in seen for c in u['callee_bridges']))
 check(u['id']+' assigned function domains',all(v['caller_domain_to_establish'] for v in D['functions'] if v['bridge_unit']==u['id']))
 seen.add(u['id'])
check('all functions assigned one proposed bridge unit',all(v['bridge_unit'] in seen for v in D['functions']))
check('exactly thirteen cited closed leaves',len(D['closed_leaves'])==13)
check('only private Dot opaque leaf reached by TX2', [v['function'] for v in D['closed_leaves'] if v['reached_in_tx2']]==['canonical::Dot::push'])
for l in D['closed_leaves']:check(l['function']+' cited packet exists',(R/l['evidence']).is_file())
check('source counts',D['counts']['functions']==len(D['functions']) and D['counts']['files']==len(files))
check('no Kani Rust or Lean runs',all(D['counts'][k]==0 for k in ('lean_attempts','kani_runs','rust_runs')))
# Prevent attributing historical frozen bytes to a changed checked-out native tree.
changed=subprocess.check_output(['git','diff','--name-only',rev,'HEAD','--','crates/','programs/'],cwd=R,text=True).splitlines()
check('all repository crates/programs byte-identical frozen -> inventory HEAD',not changed)
check('all inventoried files match frozen in working tree',all((R/f).read_bytes()==b for f,b in files.items()))
shipped_dirty=subprocess.check_output(['git','diff','--name-only','HEAD','--','crates/','programs/'],cwd=R,text=True).splitlines()
check('no working-tree shipped change',not shipped_dirty)
check('headline and no-premise-removal scope',D['headline']=='AspisR1.RPx_Deployed.deployed' and 'No premise' in D['assumptions'])
# Installed op22 is concrete; op53 is explicitly not credited to the fixture-only installation.
enc=next(v for v in D['functions'] if v['short_name']=='encode_pool_v1_pair_forest_terminal_statement_v1')
check('op22 installed concrete codec recorded',enc['abstract_adapter_slot'] is None and any(c['name']=='AspisS6CurrentCodecInstallation.encode' for c in enc['cohort_definitions']))
emit=next(v for v in D['functions'] if v['name']=='emit_result')
check('op53 modelling gap retained',emit['abstract_adapter_slot']==53 and emit['modelling_gap'] and not emit['cohort_definitions'])
check('JHb fixture not treated as adopted cohort',not any(c['name'].startswith('AspisR1.JHb') for v in D['functions'] for c in v['cohort_definitions']))
# Commit/evidence boundary: no binary/object/archive artifacts in this task.
check('no binary artifacts in task directory',not any(p.suffix in ('.olean','.o','.so','.dylib','.elf','.tar','.gz') for p in O.iterdir()))
wall=time.monotonic()-start; ru=resource.getrusage(resource.RUSAGE_SELF);cru=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt={'claim':'Source/body/dependency-name/inventory-integrity checks only; not native/model equivalence or formal release replay','target':'evidence/native-inv2-20261027/NBI2_INVENTORY.{md,json}','command':['python3','-B','evidence/native-inv2-20261027/NBI2_validate.py'],'exit_status':0,'wall_seconds':wall,'peak_rss_kib_self':ru.ru_maxrss/1024 if sys.platform=='darwin' else ru.ru_maxrss,'peak_rss_kib_max_child':cru.ru_maxrss/1024 if sys.platform=='darwin' else cru.ru_maxrss,'swap_self':ru.ru_nswap,'swap_children':cru.ru_nswap,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'frozen_revision':rev,'python':platform.python_version(),'axioms':'N/A: no new theorem or Lean compile; no new axiom introduced','host_scope':'N/A: no Lean/Kani/Rust/SBF run; no host submission or cache read/write','budgets':{'lean_used':0,'lean_limit':30,'kani_used':0,'kani_limit':0,'rust_used':0,'rust_limit':0},'source_to_elf':'Inherited Low2 pins only; no shipped-file change and no new ELF rebuild','parser_diagnostics':'tree-sitter0.26.0 exited138 (bus error) twice during local source inspection; replaced with0.25.2 / tree-sitter-rust0.24.2, parser completed. No proof attempt, timeout, memory kill or cap increase. Subsequent runner repairs only improved local dispatch/closure/index coverage and slot classification.','checks_passed':len(checks),'checks':checks,'inventoried_files':{f:sha(b) for f,b in files.items()},'input_artifacts':{str(p.relative_to(R)):sha(p.read_bytes()) for p in [reachpath,R/'evidence/replay-deployed2-20261027/RPx_import-closure-check.json',R/'evidence/replay-deployed2-20261027/RPx_plan.json',R/'evidence/replay-tops3-20261027/RPv_plan.json',R/'evidence/replay-tops3-20261027/RPv_FJv_Top-import-closure-check.json']},'script_hashes':{p.name:sha(p.read_bytes()) for p in sorted(O.glob('NBI2_*.py'))},'output_hashes':{p.name:sha(p.read_bytes()) for p in [O/'NBI2_INVENTORY.md',O/'NBI2_INVENTORY.json']}}
(O/'NBI2_VALIDATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ('exit_status','wall_seconds','peak_rss_kib_self','peak_rss_kib_max_child','swap_self','swap_children','checks_passed','source_revision')}))
