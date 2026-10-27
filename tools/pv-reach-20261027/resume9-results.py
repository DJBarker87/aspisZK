"""Validate every receipt, preserve failures, and compare unchanged row claims."""
import pathlib,json,hashlib,re,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume9';final='--final' in sys.argv
records=[];failures=[];modules=[];allowed={'propext','Classical.choice','Quot.sound'};unexpected=[]
for p in sorted(E.glob('receipt-[0-9]*.json')):
 r=json.load(open(p));a=r['attempt'];assert 40200<=a<=40299
 assert r['plan']['caps']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000)
 assert json.load(open(E/f'reservation-{a}.json'))['allowed'] is True
 tim=(E/f'time-{a}.log').read_text()
 def metric(pattern):
  m=re.search(pattern,tim);return int(m[1]) if m else None
 entry=dict(attempt=a,targets=[x['module'] for x in r['modules']],exit=metric(r'Exit status: (\d+)'),wall_seconds=r['wall_seconds'],peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),aggregate_rss_sample_peak_bytes=r['aggregate_rss_peak_bytes'],swaps=metric(r'Swaps: (\d+)'),swap_peak_bytes=r['swap_peak_bytes'],source_revision=r['source_revision'],accepted=r['accepted'],receipt=p.name,axioms=[line for x in r['modules'] for line in x.get('axioms',[])])
 assert entry['exit'] is not None and entry['peak_rss_kib'] is not None and entry['swaps']==0 and entry['swap_peak_bytes']==0
 entry['scope_wall']=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)',tim)[1]
 records.append(entry)
 for x in r['modules']:
  assert x.get('exit') is not None,(a,x['module'])
  data=subprocess.check_output(['git','show',x['source']['blob']]);assert hashlib.sha256(data).hexdigest()==x['source']['sha256']
  m=dict(attempt=a,module=x['module'],source_authority=x['source']['authority'],source_path=x['source']['path'],source_revision=x['source']['revision'],source_blob=x['source']['blob'],source_sha256=x['source']['sha256'],object_sha256=x['object_sha256'],exit=x['exit'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],accepted=x['accepted'],axioms=x['axioms'])
  m['wall']=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)',x['time_log'])[1]
  modules.append(m)
  if x['accepted']:
   assert x['object_sha256'] and 'sorryAx' not in x['output']
   for ax in x['axioms']:
    match=re.search(r'depends on axioms: \[([^\]]*)\]',ax)
    names={n.strip() for n in match[1].split(',')} if match else set()
    if names-allowed:unexpected.append(dict(attempt=a,module=x['module'],line=ax,unexpected=sorted(names-allowed)))
  else:failures.append(dict(attempt=a,module=x['module'],source_sha256=x['source']['sha256'],exit=x['exit'],output=x['output'],retained_unchanged=True,credit=False))
assert len({r['attempt'] for r in records})==len(records)
if final:
 assert len(records)==100 and {r['attempt'] for r in records}==set(range(40200,40300))
 assert all(r['accepted'] for r in records if r['attempt']>=40297)
 assert not unexpected,unexpected
summary=dict(charged_attempts=len(records),accepted=sum(r['accepted'] for r in records),failed=sum(not r['accepted'] for r in records),lean_process_invocations=len(modules),kani=0,ids=[r['attempt'] for r in records],chunk_attempts=7,prerequisite_modules_in_chunks=200,native_modules_accepted=sum(40210<=x['attempt']<=40296 and x['accepted'] for x in modules),maximum_scope_peak_rss_kib=max(r['peak_rss_kib'] for r in records),maximum_aggregate_rss_sample_peak_bytes=max(r['aggregate_rss_sample_peak_bytes'] for r in records),swaps=sum(r['swaps'] for r in records),unexpected_accepted_axioms=unexpected,audit_attempts=[r for r in records if r['attempt']>=40297],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),final=final)
for f,d in [('receipt-index.json',records),('module-index.json',modules),('failures.json',failures),('TALLY.json',summary)]:
 (E/f).write_text(json.dumps(d,indent=2)+'\n')
old=json.load(open(E.parent/'resume8/row-comparison.json'));old.update(selected_dictionary_installed_op84=True,installed_theorem='R1Z.PV_RE_InstalledOp84B9.installed_noCatch',actual_client_to_nonce_store='R1Z.PV_RE_ReserveGuards9.client_to_store',native_fixture_success=False,native_nonvacuity=False,complete_reached_set_transfer=None,complete_reached_set_withdrawal=None,universally_excluded_entries_after=[],after=dict(V404='OPEN',V405='OPEN'))
(E/'row-comparison.json').write_text(json.dumps(old,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['charged_attempts','accepted','failed','lean_process_invocations','native_modules_accepted','maximum_scope_peak_rss_kib','swaps']},indent=2))
