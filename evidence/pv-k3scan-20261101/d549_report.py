"""Update this audit's scoped recommendations from retained receipts; never edits the ledger."""
from pathlib import Path
import subprocess,json,lzma,hashlib,re,collections
E=Path(__file__).resolve().parent;BASE='bad175c553'
def frozen(name):return subprocess.check_output(['git','show',BASE+':evidence/pv-k3scan-20261101/'+name])
credits=json.loads(lzma.decompress(frozen('CREDITS.json.xz')));coverage=json.loads(frozen('ROW-COVERAGE.json'));results=[];pairs=[]
for i in range(60):
 ident=f'K792{i:02d}';p=E/'host'/ident
 if not (p/'receipt.json').exists():continue
 r=json.loads((p/'receipt.json').read_text());log=(p/'output.log').read_text();a=json.loads((p/'admission.json').read_text());b=json.loads((p/'barrier.json').read_text())
 assert a['allowed'] and b['allowed'];assert b['own_limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 kind='PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'EXPECTED_CONTROL_FAIL' if r['negative_control'] and 'VERIFICATION:- FAILED' in log else 'SETUP_FAILURE' if 'could not compile' in log or 'Failed to execute cargo' in log else 'TIMEOUT' if r['exit_status']==124 else 'UNRESOLVED'
 m=re.search(r'\*\* (\d+) of (\d+) failed',log);s=json.loads((p/'STARTED.json').read_text())
 results.append({'id':ident,'result':kind,'receipt':'host/'+ident+'/receipt.json','epoch':s['epoch'],**{k:r.get(k)for k in ['exit_status','wall_seconds','peak_rss_kib','swap','source_revision','print_axioms']},'resolved_revision':subprocess.check_output(['git','rev-parse',r['source_revision']],text=True).strip() if r.get('source_revision') else None,'failed_checks':int(m[1])if m else None,'total_checks':int(m[2])if m else None,'original_credit':r.get('config',{}).get('original_credit'),'config':r.get('config',{}),'symbols_available':(p/'symbols-index.json').exists()})
byid={r['id']:r for r in results}
assert len(results)<=60
for a,b in zip(results,results[1:]):assert b['epoch']-a['epoch']>=180,(a['id'],b['id'])
# The first pair was completed before D549. Its independently retained validation stands.
pairs.append({'credit_ids':['C044'],'positive':'K79200','control':'K79201','complete':True,'scope':'selected PathBuf gate; independent std transfer withheld'})
for p in results:
 if p['result']!='PASS' or not p['original_credit']:continue
 nxt=f"K{int(p['id'][1:])+1}";n=byid.get(nxt)
 if n and n['result']=='EXPECTED_CONTROL_FAIL' and n['original_credit']==p['original_credit']:
  assert n['failed_checks'] and n['failed_checks']>=1
  # No UB/unwinding failure is accepted as the matched property mutation.
  text=(E/'host'/nxt/'output.log').read_text()
  assert 'unwinding assertion' not in text.lower(),nxt
  pairs.append({'credit_ids':[p['original_credit']],'positive':p['id'],'control':nxt,'complete':True,'scope':p['config']['harness'],'positive_checks':p['total_checks'],'control_failed_checks':n['failed_checks']})
for pair in pairs:
 for cid in pair['credit_ids']:
  x=next(x for x in credits if x['credit_id']==cid);old_status=x['final_status'];x['inherited_final_status']=old_status;x['fresh_pair']=pair
  x['k3_rerun_status']='PASS_WITH_MATCHED_FAILING_CONTROL';x['rerun']=pair['positive']+' PASS / '+pair['control']+' matched control FAIL; original names/domain/bounds retained';x['matched_control']='host/'+pair['control']+'/receipt.json'
  inherited_k1='historical K-1 copy suspension' in x['reason'];x['inherited_k1_suspension']=inherited_k1
  if inherited_k1:
   x['final_status']='SUSPENDED';x['reason']='Fresh K-3 scoped check passed with matched failure. Independent historical K-1 copy suspension is retained; no deployed restoration.'
  elif x['classification'] in ['UNAFFECTED','NOT-EXPOSED']:
   x['final_status']='UNAFFECTED';x['reason']='Original selected K-3 classification retained; fresh controlled pair passes. All separate native/std/compiler qualifications retained.'
  else:
   x['final_status']='RESTORED';x['reason']='RESTORED for this exact bounded K-3 credit only: recovered selected source closure, no writable harness/stub/oracle static, positive PASS and matched assertion FAIL. No full-row or deployed std transfer.'
  x['deployed_transfer']='WITHHELD unless independently discharged at the original source/std/compiler/world boundary; this campaign does not certify it.'
for cid,kind,reason in [('C051','native Token::drop log','DROPS is written inside Token::drop; no checked local-context association. Never replaced by a local mock.'),('C053','native Core::default seed','DEFAULT_STATE is written by the harness and read inside the parameterless Core::default trait step. No checked local-context association.')]:
 x=next(x for x in credits if x['credit_id']==cid);x['final_status']='SUSPENDED';x['native_step_static']=kind;x['rerun_stop']=reason
for cid in ['C156','C163','C164']:
 x=next(x for x in credits if x['credit_id']==cid);x['final_status']='SUSPENDED';x['rerun_stop']='Original shared_callee16 memo oracle writes USED/TAG/LEFT/RIGHT/OUTPUT. No local-context shared-callee/native-step association supplied; not cleared by the independent local sum replays.'
complete=len(results)==60
raw=(json.dumps(credits,indent=2)+'\n').encode();(E/'CREDITS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'CREDITS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
summary={'campaign_in_progress':not complete,'budget_invocations':60,'charged_invocations':len(results),'initial_spent':2,'Lean':0,'results':results,'pairs':pairs,'counts':dict(collections.Counter(x['result']for x in results)),'credit_status':dict(collections.Counter(x['final_status']for x in credits)),'endpoint_premises_removed_added_weakened':[0,0,0],'deployed_transfer':'WITHHELD; K-3 scoped replay is separate from std, K-1/K-2, native world and compiler transfer'}
(E/'D549-RESULTS.json').write_text(json.dumps(summary,indent=2)+'\n')
old=frozen('K3-CREDITS.md').decode();table=old.split('\n## Controlled re-run and limits')[0]
for x in credits:
 line=next(l for l in table.splitlines()if l.startswith('| '+x['credit_id']+' |'))
 cols=line.split(' | ');cols[-1]=x['rerun']+'; **'+x['final_status']+'** |';table=table.replace(line,' | '.join(cols))
extra='''\n## D549 controlled continuation (authoritative latest disposition)\n\nThe user counts both properties and controls against sixty invocations. K79200/K79201 were the two already spent. The historical PINS.json field naming sixty pairs is superseded by D549-RUN-PLAN.json. D549-RESULTS.json contains exact targets, exits, resource measurements, revisions and N/A axioms through the current checkpoint. No ledger was edited.\n\nRESTORED is a scoped K-3 recommendation only. Historical K-1 suspensions remain SUSPENDED even after a fresh K-3 pair; k3_rerun_status distinguishes that fact in CREDITS.json.xz. Standard-library/deployed transfer is not inferred from a passing control. The prior PathBuf parity audit remains withheld for its differing and unresolved items; every new exact reached-symbol set is retained for independent per-item review. Compiler/runtime V370 and D381/D386, world/allocator adequacy, E1/E2, proof-account client and L1/L2/L3 remain.\n\nV183's op32 family is actually selected at runjoin63 opsNative. Its current ReserveSelected/AllocatorWorld structural source packet is independent of C018/C019/C029. The bounded reserve pairs do not prove a universal world-free allocator callback. Other touched installed op51/op120/op249/op253 selections retain their independent qualified structural/extraction scopes. V185's original Word/Error length gate and V244's two currently consumed Kani local bodies were checked before the lower-priority historical mask packets. Original names and domains are retained; unused global memo proof modules were excluded only from the independently selected local-body packages. These exclusions do not supply a replacement shared-callee law.\n\nImmutable recovery: D038-updates, candidate/c3/include snapshots, K72122/K72135 run inputs, K26/K28 frozen source inventories and retained historical LLBC source contents. Every recovered byte is hash-checked. Original selected macro constants, original KMX stubs and their complete source modules remain recorded in the source payloads and closure dossiers. No current same-name file silently replaces a missing original. The complementary split packets retain all six original stubs and their original bounds; they do not release C002's historical no-stub route.\n\nNative-step statics still SUSPENDED: C051 empty_gate::empty_noncopy_length_branches (Token::drop/DROPS); C053 generic_default_gate::wrapper_default_arbitrary_core (Core::default/DEFAULT_STATE). Shared memo credits C156 equivalence16::shared_repeat16 and C163/C164 old sum_high_nodes/sum_high_path also remain SUSPENDED. No local mock is substituted for those native/stub steps.\n\nSetup failures are retained: K79206-preflight failed cargo metadata before any compiler/scope, uncharged, then recovered the omitted pinned c3/include directories. K79208 was a charged compiler/setup failure on an omitted frozen tree_reference file; K79209 used the repaired, explicitly recorded module/literal closure. No property was checked in K79208 and no failure was hidden. K79207's one expected assertion panic used Kani's runtime-format placeholder; A direct-spelling control for that same false inequality was prepared but not launched; its slot was consumed by the retained K79219 path setup failure. K79220 corrects only the module path, not any source/native property.\n'''
extra+='\nCampaign '+('complete at sixty charged invocations.' if complete else 'IN PROGRESS; allowance is not yet exhausted.')+' '+str(len(pairs))+' complete retained property/control pairs.\n'
extra+='\n| Pair credit | Positive | Matched control | Scope |\n|---|---|---|---|\n'+''.join('| '+', '.join(p['credit_ids'])+' | '+p['positive']+' PASS | '+p['control']+' FAIL | `'+p['scope']+'` |\n'for p in pairs)
(E/'K3-CREDITS.md').write_text(table+extra)
print(json.dumps({'invocations':len(results),'pairs':len(pairs),'counts':summary['counts'],'statuses':summary['credit_status']}))
