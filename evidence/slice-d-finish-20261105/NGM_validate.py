from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1]
def read(n):return json.loads((E/n).read_text())
def receipt(a):
 x=read(a+'/receipt.json');assert x['attempt']==a
 assert x['swaps']=='0';assert x['source_revision'];assert x['command'];assert x['wall_seconds']>=0;assert int(x['peak_rss_kib'])>0
 admission=read(a+'-admission.json');assert admission['exit']==0 and admission['reservation']['allowed']is True
 return x
closed=read('NGM_CLOSED.json');delta=read('NGM_LEDGER_DELTA.json');audit=read('NGM_AUDIT.json')
base=json.loads(lzma.decompress((P/delta['baseline']).read_bytes()));rows={r['row']:r for r in base['rows']}
assert delta['no_other_status_change']and delta['not_a_premise_retirement']
assert set(delta['new_closed_rows'])=={r for c in closed['functions']for r in c['rows']}
for c in closed['functions']:
 for row in c['rows']:assert rows[row]['function']==c['function']and rows[row]['composed_status']=='OPEN'
 for a,expected in [(c['native_positive'],0),(c['matched_control'],1)]+[(a,i)for i,a in enumerate(c['copy_pair'])]:
  x=receipt(a);assert x['exit_status']==expected
  g=read(a+'-graph-check.json');assert g['graph_matches_frozen']and not g['new_package_tuples']and not g['edge_errors']
  assert g['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  lock=read(a+'-lock-check.json');assert lock['unchanged']and lock['before']==lock['after']==g['lock_sha256']
  assert not read(a+'-source-check.json')['errors']
  package=next(p for p in g['selected_closure']if p['name']=='aspis-r1-cost-probe')
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(package['features'])
  assert x['env']['CARGO_NET_OFFLINE']=='true'
  log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL'if expected==0 else'VERIFICATION:- FAILED')in log
 positive=receipt(c['native_positive']);negative=receipt(c['matched_control']);assert positive['module']==negative['module']
 if c['function'].endswith('::shared_two_point_guard'):
  assert 'NGM_weights::guard_raw_post' in (E/c['matched_control']/'stdout.log').read_text()
  src=(E/c['native_positive']/'sources/NGM_src/crates/aspis-r1-cost-probe/src/weights.rs').read_text()
  frozen=subprocess.check_output(['git','show',closed['frozen_revision']+':crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
  sig='fn shared_two_point_guard(';lo=frozen.index(sig);hi=frozen.index('\n }',lo)+3;assert frozen[lo:hi]in src
  raw=read('NGM_final_audit/proof0.json')['results']
 elif c['function'].endswith('::double'):
  assert read('NGM_DOUBLE_ERASURE.json')['status']=='PASS source erasure only'
  assert len(c['native_pairs'])==7 and not c['inner_hypotheses_remaining']
  for pair in c['native_pairs']:
   for offset,a in enumerate(pair):
    r=receipt(a);assert r['exit_status']==offset
    log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL'if offset==0 else'VERIFICATION:- FAILED')in log
    assert not re.search(r'TIMEOUT|timed out|memory limit exceeded|SIGKILL',log,re.I)
    assert read(a+'-graph-check.json')['graph_matches_frozen']and read(a+'-lock-check.json')['unchanged']
   assert receipt(pair[0])['module']==receipt(pair[1])['module']
  raw=[json.loads(line[11:])for line in(E/'NGM_L055/stdout.log').read_text().splitlines()if line.startswith('NEP_RESULT ')]
  assert c['paired_product_law']in {r['root']for r in raw}
  for suffix in ['QM31::mul','QM31::add','QM31::sub']:
   selected=[r for r in base['rows']if r['function']=='crates/aspis-core/src/field.rs::'+suffix];assert selected and all(r['composed_status']=='CLOSED'for r in selected)
  assert read('NGM_E002-extraction-pins.json')['reference_sha256']==hashlib.sha256((E/'NGM_double_reference.rs.txt').read_bytes()).hexdigest()
 else:raise AssertionError('Unreviewed promotion')
 result=next(r for r in raw if r['root']==c['lean_root']);assert result['equal']and set(result['walked_axioms'])==set(result['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
assert audit['standard_axioms_only']and audit['dangling']==audit['incompatible_owners']==audit['import_mismatches']==0
for a in [audit['combined_attempt'],audit['scan_attempt']]:assert receipt(a)['exit_status']==0
scan=[json.loads(l)for l in (E/'NGM_LOADED_scan.jsonl').read_text().splitlines()];assert len(scan)==audit['modules'];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert (E/'NGM_COMBINED_IMPORT.lean').read_text().startswith('import NGJ_VERIFIER_IMPORT')
for a in ['NGM_L003','NGM_L004','NGM_L005','NGM_L011','NGM_L012','NGM_L017','NGM_L018']:assert receipt(a)['exit_status']==0
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,str(p)
# Final packet additions only: no baseline acceptance check is removed.
if (E/'NGM_BUDGET.json').exists():
 journal=[json.loads(line)for line in(E/'NGM_ATTEMPTS.jsonl').read_text().splitlines()]
 expected={f'NGM_{kind}{number:03}'for kind,count in [('K',100),('L',70),('E',3)]for number in range(1,count+1)}
 assert len(journal)==len(expected)==173 and {r['attempt']for r in journal}==expected
 for a in sorted(expected):
  r=receipt(a)
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert int(r['peak_rss_kib'])*1024<8589934592
  if a.startswith('NGM_K'):
   g=read(a+'-graph-check.json');lock=read(a+'-lock-check.json')
   assert g['graph_matches_frozen']and not g['new_package_tuples']and not g['edge_errors']
   assert lock['unchanged']and lock['before']==lock['after']==g['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   assert r['env']['CARGO_NET_OFFLINE']=='true'and not read(a+'-source-check.json')['errors']
   package=next(p for p in g['selected_closure']if p['name']=='aspis-r1-cost-probe')
   assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(package['features'])
 budget=read('NGM_BUDGET.json');assert budget['used']==budget['limit']==dict(kani=100,lean_audit=70,extraction=3)
 assert budget['kani']['excluded']==['NGM_K083','NGM_K086','NGM_K087']
 pairs=[(i,i+1)for i in range(1,83,2)]+[(84,85)]+[(i,i+1)for i in range(88,100,2)]
 for positive,negative in pairs:
  for number,expected_exit in [(positive,0),(negative,1)]:
   a=f'NGM_K{number:03}';raw=(E/a/'stdout.log').read_text();assert receipt(a)['exit_status']==expected_exit
   assert ('VERIFICATION:- SUCCESSFUL'if expected_exit==0 else'VERIFICATION:- FAILED')in raw
   assert not re.search(r'timed out|memory limit exceeded|SIGKILL',raw,re.I)
  assert receipt(f'NGM_K{positive:03}')['module']==receipt(f'NGM_K{negative:03}')['module']
 for a in budget['kani']['excluded']:assert 'timed out'in(E/a/'stdout.log').read_text()
 all_raw=read('NGM_final_audit/proof0.json')['results']
 for a in ['NGM_L055','NGM_L069']:
  assert receipt(a)['exit_status']==0
  all_raw += [json.loads(line[11:])for line in(E/a/'stdout.log').read_text().splitlines()if line.startswith('NEP_RESULT ')]
 declared={n for group in read('NGM_AUDIT_ROOTS.json')['groups']for n in group}
 assert {r['root']for r in all_raw}==declared and len(declared)==audit['unique_walked_roots']==109
 assert all(r['equal']and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in all_raw)
 for item in read('NGM_INPUT_INDEX.json')['inputs']:
  p=E/item['path'];target=E/item['stored'];assert p.is_symlink()and p.resolve()==target.resolve()
  assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256']
 assert read('NGM_HELPER_ERASURE.json')['status'].startswith('PASS')and len(read('NGM_HELPER_ERASURE.json')['mutations'])==6
 assert all(x['rejected']for x in read('NGM_HELPER_ERASURE.json')['mutations'])
 assert len(read('NGM_REMAINING.json'))==24 and all(r['status']=='OPEN'for r in read('NGM_REMAINING.json'))
print(json.dumps(dict(status='PASS',new_closed_rows=delta['new_closed_rows'],root_status=closed['driver_root_status'],raw_roots=audit['raw_roots'],modules=audit['modules'],scope='additive NGM delta; baseline immutable')))
