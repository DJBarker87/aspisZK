"""Adapt NEH_summary's explicit PASS/FAIL pairing; add closure and gate checks.
No authoritative ledger is modified. Raw receipt verdicts never imply adoption.
"""
from NEK_scan import *
from NEK_verdict import verdict
from pathlib import Path

def get(path):
 p=ROOT/path
 b=p.read_bytes() if p.exists() else subprocess.check_output(['git','show','HEAD:'+path])
 return json.loads(lzma.decompress(b) if path.endswith('.xz') else b)
old=get('evidence/k3-audit-20261030/NEH_LEDGER_DELTA.json');app=get('evidence/k3-audit-20261030/NEH_APPLICABILITY.json');C=read_json(E/'NEK_CLOSURE.json')
base={q['receipt']:dict(q) for q in old['receipts']};appby={q['receipt']:q for q in app['receipts']};attempts=[json.loads(l) for l in (E/'NEK_ATTEMPTS.jsonl').read_text().splitlines()]
runs={};byid={}
for r in attempts:
 if r['kind']!='kani':continue
 a=r['attempt'];v=verdict((E/a/'stdout.log').read_text());ni=r['native_command'];q=dict(attempt=a,verdict=v,exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],harness=ni[ni.index('--harness')+1],receipt=str((E/a/'receipt.json').relative_to(ROOT)))
 byid[a]=q;rp=r['deps_fingerprint']['original_receipt'];runs.setdefault(rp,[]).append(q)
wanted={k['receipt'] for row in C['rows'] for k in row['closure']['kani']}
for rp in wanted:
 if rp not in base:
  r=get(rp);base[rp]=dict(receipt=rp,harness=r.get('module'),outcome='OPEN',reason='not in NEH selected support; reviewed here',groups=[],claims=[],dependent_rows=[])
# Only expanded added-module paths are promoted to unaffected. Existing K-2,
# K-1, source/model association and external dependency/tool trust remain.
for r in read_json(E/'NEK_EXPANSION_AUDIT.json'):
 if r['status']=='UNAFFECTED_EXPANDED':base[r['receipt']].update(outcome='UNAFFECTED_EXPANDED',reason='receipt-pinned added sources and include/module paths expanded; no writable storage in the selected closure',evidence='NEK_EXPANSION_AUDIT.json')
for r in read_json(E/'NEK_KNF_SOURCE_AUDIT.json'):
 base[r['receipt']].update(outcome='UNAFFECTED_EXPANDED',reason='three exact standalone modules and qualified builtin macros audited; no writable storage',evidence='NEK_KNF_SOURCE_AUDIT.json')
ndn='evidence/native-front2b-20261028/NDN_K001/receipt.json';base[ndn].update(outcome='OPEN',reason='inherited written-static module found through the pinned input manifest; requires exact NDN replay')
# Pure active NEE certificates supersede historical flat lists, not their verdicts.
for r in read_json(E/'NEK_NEE_ACTIVE_AUDIT.json'):
 for s in r['certified_active_support']:
  base[s['receipt']].update(outcome='UNAFFECTED_EXPANDED',reason='exact active pure payment-frame source/patch/graph audited; historical orphan oracle module not loaded',evidence='NEK_NEE_ACTIVE_AUDIT.json')

def good(a,v):return a in byid and byid[a]['verdict']==v
restored={};gates=[]
def pair(a,b):return good(a,'PASS') and good(b,'FAIL')
def gate(name,pairs):
 ok=all(pair(a,b) for a,b in pairs);gates.append(dict(name=name,pairs=pairs,closed=ok));return ok
cfg={}
for name,a in [('matrix',336),('scan',338),('simple',340)]:cfg[name]=gate('KMX '+name,[(f'NEK_K{a:03}',f'NEK_K{a+1:03}')])
program_copy=gate('KMX deployed program base',[('NEK_K309','NEK_K310')])
def clear(rps,a,b,reason,admitted=True):
 if pair(a,b) and admitted:
  for rp in rps:
   if rp in base:restored[rp]=dict(positive=a,control=b,reason=reason)
# Same original property/name and local native-step log.
specs=[(1,2,['evidence/native-front2-20261028/NDE_K050/receipt.json'],cfg['matrix']), (3,4,['evidence/native-front2-20261028/NDE_K052/receipt.json'],cfg['scan']), (5,6,['evidence/native-tx2a-20261027/NBC_K003/receipt.json'],True), (7,8,['evidence/native-front2-20261028/NDE_K071/receipt.json','evidence/native-front2-20261028/NDE_K072/receipt.json'],cfg['simple']), (9,10,['evidence/native-tx2c-20261027/NBG_K028/receipt.json'],True), (13,14,['evidence/native-tx2g-20261028/NBP_K002/receipt.json'],program_copy), (15,16,['evidence/native-front2-20261028/NDE_K008/receipt.json','evidence/native-front2-20261028/NDE_K009/receipt.json'],True), (195,196,['evidence/native-tx2h-20261028/NBQ_K016/receipt.json'],True), (303,304,[ndn],cfg['matrix']), (342,343,['evidence/native-tx2g-20261028/NBP_K040/receipt.json'],program_copy)]
for a,b,rps,admitted in specs:clear(rps,f'NEK_K{a:03}',f'NEK_K{b:03}','same-name local-record proof/control; native-step/domain/Lean and copy configuration associations retained',admitted)
for a in list(range(99,117,2))+[118]:
 aa=f'NEK_K{a:03}';bb=f'NEK_K{a+1:03}'
 if aa in byid and bb in byid:
  originals=[r['deps_fingerprint']['original_receipt'] for r in attempts if r['attempt'] in [aa,bb]]
  clear(originals,aa,bb,'isolated exact pure original contract; unrelated static log functions omitted',cfg['simple'] if a==118 else pair('NEK_K015','NEK_K016'))
for a,b in [(17,18),(207,20),(21,22),(204,205)]:
 aa=f'NEK_K{a:03}';bb=f'NEK_K{b:03}'
 originals=[r['deps_fingerprint']['original_receipt'] for r in attempts if r['attempt'] in [aa,bb]]
 clear(originals,aa,bb,'exact imported NEA support; explicit point/line context, inverse native body projection, named existing Lean product laws; original domain retained')
for a in [305]:
 aa=f'NEK_K{a:03}';bb=f'NEK_K{a+1:03}';originals=[r['deps_fingerprint']['original_receipt'] for r in attempts if r['attempt'] in [aa,bb]];clear(originals,aa,bb,'original selected KMX configuration control, static-free isolated module')
if program_copy:
 for a in ['NEK_K309','NEK_K310']:
  rp=next(r['deps_fingerprint']['original_receipt'] for r in attempts if r['attempt']==a)
  clear([rp],'NEK_K309','NEK_K310','original program KMX configuration control')
# Thirty native conjuncts, each paired independently. The timed-out K052
# negative is replaced by two strictly smaller nibble relations, not retried.
uint_assembly=(E/'NEK_L003/receipt.json').exists() and read_json(E/'NEK_L003/receipt.json')['exit_status']==0
common_shape=uint_assembly and gate('Box common fidelity',[('NEK_K190','NEK_K191'),('NEK_K192','NEK_K194')]) and good('NEK_K197','FAIL') and pair('NEK_K219','NEK_K220')
plan=read_json(E/'NEK_COMMON_BATCH_PLAN_v2.json');parts=[]
for i in range(30):
 pp=next(q for q in plan if q['cfg']==f'NEK_clause_{i}' and not q['negative']);nn=next(q for q in plan if q['cfg']==f'NEK_clause_{i}' and q['negative'])
 ps=[q for q in byid.values() if q['attempt']==pp['attempt']];positive=bool(ps and ps[0]['verdict']=='PASS');control=good(nn['attempt'],'FAIL')
 if nn['attempt']=='NEK_K052':
  control=pair('NEK_K235','NEK_K236') and pair('NEK_K237','NEK_K238') and all(pair(f'NEK_K{x:03}',f'NEK_K{y:03}') for x,y in [(335,328),(329,330),(331,332),(333,334)])
 cp=pair(f'NEK_K{130+2*i:03}',f'NEK_K{131+2*i:03}')
 parts.append(dict(original_receipt=pp['original_receipt'],conjunct=pp['clause'],predicate=pp['predicate'],positive=pp['attempt'],control=nn['attempt'],control_replaced_by_nibbles=nn['attempt']=='NEK_K052',native_window_closed=positive and control,copy_closed=cp,closed=positive and control and cp and common_shape))
nec=get('evidence/slice-s-leaves-20261029/NEC_CLOSED.json')
common_cert=[]
for rp,neg in zip(nec[0]['kani_receipt_paths'],nec[0]['control_receipts']):
 ss=[q for q in parts if q['original_receipt']==rp];ok=bool(ss) and all(q['closed'] for q in ss)
 common_cert.append(dict(positive_receipt=rp,historical_control=neg,closed=ok,conjuncts=ss,assembly='conjunction of native windows, arbitrary bounded local indices; K052 relation assembled by NEK_UIntWindows.byte_nibbles_ext (L003) and NEK_ByteWindows.quotient_remainder_ext; native UInt8 tool transport retained'))
 if ok:
  for q in [rp,neg]:restored[q]=dict(reason='original property assembled from all paired native conjuncts; full Box shape/copy admission; original name/domain retained',windows=[x['positive'] for x in ss],controls=[x['control'] for x in ss],reclassification='explicit native contract semantic transport remains P6/D188 trust; not trust removal')
after_shape=gate('Result<Box<After>,Error> fidelity',[('NEK_K313','NEK_K314'),('NEK_K315','NEK_K316')]) and good('NEK_K317','FAIL') and pair('NEK_K318','NEK_K319')
for a,b in [(120,121),(122,123),(198,199),(200,201),(202,203)]:
 aa=f'NEK_K{a:03}';bb=f'NEK_K{b:03}';originals=[r['deps_fingerprint']['original_receipt'] for r in attempts if r['attempt'] in [aa,bb]]
 clear(originals,aa,bb,'full original decoder property/frame; explicit child/log record; shape and exact KMX admission; inverse native child-call association retained',after_shape)
for rp,p in restored.items():base[rp].update(outcome='RESTORED',reason=p['reason'],pair=p)
# Imported receipt duplicates are reused only on complete byte identity.
byhash=collections.defaultdict(list)
for rp in base:
 try:b=(ROOT/rp).read_bytes() if (ROOT/rp).exists() else subprocess.check_output(['git','show','HEAD:'+rp]);byhash[sha(b)].append(rp)
 except Exception:pass
aliases=[]
for h,paths in byhash.items():
 refs=[p for p in paths if base[p]['outcome'] in ['RESTORED','UNAFFECTED_EXPANDED']]
 if not refs:continue
 source=sorted(refs,key=lambda p:('IMPORTED' in p,p))[0]
 for p in paths:
  if p==source:continue
  if base[p]['outcome'] not in ['RESTORED','UNAFFECTED_EXPANDED']:
   base[p].update(outcome=base[source]['outcome'],reason='exact-byte receipt alias of '+source,alias_of=source)
  aliases.append(dict(receipt=p,canonical=source,receipt_sha256=h))
clears={'RESTORED','UNAFFECTED_EXPANDED'}
rows=[]
for r in C['rows']:
 support=r['closure']['kani'];blocked=[q['receipt'] for q in support if base[q['receipt']]['outcome'] not in clears]
 # NEH restored evidence is reused; ordinary recovered-only UNAFFECTED evidence
 # must have this pass's expanded closure audit to clear a transitive row.
 state=not blocked and not r['closure']['unresolved']
 rows.append(dict(row=r['row'],function=r['function'],k3_fully_cleared_including_transitive_support=state,status='K3_CLEARED' if state else 'OPEN',support_receipts=[q['receipt'] for q in support],blocked_receipts=blocked,unresolved=r['closure']['unresolved'],functions=r['closure']['functions'],edges=r['closure']['edges'],historical_references=r['closure']['historical_references'],scope='K-3 only; original K-1/K-2, runtime and P6/D188 trust, caller domains and authoritative adoption remain'))
counts=dict(NEB_rows=66,NEB_fully_cleared=sum(r['row'].startswith('NEB:') and r['k3_fully_cleared_including_transitive_support'] for r in rows),NEB_open=sum(r['row'].startswith('NEB:') and not r['k3_fully_cleared_including_transitive_support'] for r in rows),NEE_rows=6,NEE_cleared=sum(r['row'].startswith('NEE:') and r['k3_fully_cleared_including_transitive_support'] for r in rows))
base['evidence/native-tx2r2-20261028/NCN_K061/receipt.json'].update(reason='original Vec row contract timed out; K344 selected the weak-contract caller instead of the intended window proof and earns no window credit; next needs selected window proof/control, exact KMX/Vec shape admission and native/domain association; generic UInt64 assembly and frame laws completed in L004/L006')
receipts=[]
for rp,r in sorted(base.items()):
 q={k:v for k,v in r.items() if k not in ['runs']};q['own_runs']=runs.get(rp,[])
 if q['outcome']=='OPEN':q['remaining_obligation']=q['reason']+'; needs exact local-context native proof/control, source association and any copy/shape/domain gates; no credit from timeout or an unpaired pass'
 receipts.append(q)
ndt=[]
for r in old['rows']:
 if not r['row'].startswith('NDT:'):continue
 ss=[q for q in receipts if r['row'] in q.get('dependent_rows',[])];blocked=[q['receipt'] for q in ss if q['outcome'] not in clears and q['outcome']!='UNAFFECTED'];ndt.append(dict(row=r['row'],function=r.get('function'),k3_direct_status='OPEN' if blocked else 'K3_DIRECT_CLEARED',blocked_receipts=blocked,limitation='NDT direct inventory only; no transitive or headline adoption claim'))
for rp in ['evidence/native-tx2r2-20261028/NCN_K061/receipt.json']:
 if rp in base:base[rp]['reason']='original Vec contract timed out; requires strict byte-window proof/control, exact KMX/Vec fidelity and Lean/native assembly'
out=dict(schema='NEK-ledger-delta-v2',scope='K-3 static/constant sharing, full selected support closure of 66 NEB and 6 active NEE rows; remaining NDT credits inventoried',frozen_revision=FROZEN,authoritative_ledger_modified=False,budget=dict(kani=sum(r['kind']=='kani' for r in attempts),kani_limit=240,lean=sum(r['kind']=='lean' for r in attempts),lean_limit=10),per_slice_summary=counts,receipt_counts=dict(collections.Counter(r['outcome'] for r in receipts)),receipts=receipts,rows=rows,NDT_direct_rows=ndt,byte_identical_aliases=aliases,common_certificates=common_cert,gates=gates,formal_assembly=['NEK_ByteWindows.quotient_remainder_ext','NEK_ByteWindows.indexed_nibbles_ext','NEK_UIntWindows.byte_nibbles_ext','NEK_UIntWindows.indexed_bytes_ext','NEK_WindowFrames.writeAt_selected','NEK_WindowFrames.writeAt_frame','NEK_WindowFrames.disjoint_writes','NEK_WindowFrames.window_and_frame_ext','NEK_WindowFrames.finite_windows_ext','NEK_WordWindows.digits_ext','NEK_WordWindows.byteWindow_nat','NEK_WordWindows.word_windows_ext'],qualifications=['review-only reclassification, no authoritative adoption','P6/D188 native contract semantic transport remains explicit tool trust','K-2 Option<fn>/function-pointer-dependent quarantine remains','K-1 copy fidelity and field/loop/runtime rulings remain','AspisR1.RPx_Deployed.deployed headline unchanged'])
old_by={r['row']:r for r in old['rows'] if r['row'].startswith('NEB:')}
counts['original_10_suspended_now_cleared']=sum(r['status']=='K3_CLEARED' and old_by.get(r['row'],{}).get('k3_direct_support_status')=='SUSPENDED' for r in rows)
counts['original_10_still_open']=sum(r['status']=='OPEN' and old_by.get(r['row'],{}).get('k3_direct_support_status')=='SUSPENDED' for r in rows)
counts['original_56_now_fully_cleared']=sum(r['status']=='K3_CLEARED' and r['row'] in old_by and old_by[r['row']]['k3_direct_support_status']!='SUSPENDED' for r in rows)
counts['original_56_transitively_open']=sum(r['status']=='OPEN' and r['row'] in old_by and old_by[r['row']]['k3_direct_support_status']!='SUSPENDED' for r in rows)
C['schema']='NEK-closure-v2';C['summary']=counts
row_index={r['row']:r for r in rows}
for cr in C['rows']:
 cr['fully_cleared']=row_index[cr['row']]['k3_fully_cleared_including_transitive_support'];cr['limitation']='K-3 review only, current selected certificates and real call edges; original K-1/K-2, runtime/domain and P6/D188 trust/adoption qualifications retained'
 for kr in cr['closure']['kani']:kr['review_outcome']=base[kr['receipt']]['outcome']
(E/'NEK_CLOSURE.json').write_text(json.dumps(C,indent=2)+'\n')
(E/'NEK_LEDGER_DELTA.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# K-3 static/constant sharing reruns','','Review-only outcomes. PASS requires a matched FAIL and the listed domain, source, copy and shape gates before restoration. OPEN includes selection/compile errors and timeouts. No authoritative ledger or headline is changed.','','Budget: '+str(out['budget'])+'. Per-slice summary: '+str(counts)+'.','','| Attempt | Original receipt | Actual harness | Verdict | Exit | Wall s | Peak KiB | Swap |','|---|---|---|---|---:|---:|---:|---:|']
for r in attempts:
 if r['kind']!='kani':continue
 q=byid[r['attempt']];lines.append('| '+' | '.join([r['attempt'],r['deps_fingerprint']['original_receipt'],q['harness'],q['verdict'],str(r['exit_status']),str(round(r['wall_seconds'],3)),str(r['peak_rss_kib']),str(r['swaps'])])+' |')
lines+=['','All exact commands, source revisions and hashes, scope limits, frozen graphs and lock checks are in NEK_ATTEMPTS.jsonl and each attempt directory. K052 lacks an immediate native postcheck and earns no credit; its later read-only lock recovery is separate.','', 'The provisional NEC_K036 domain finding was retracted after exact-source inspection. No genuine semantic counterexample or historical withdrawal is reported. NDN_K001’s recovered-parent-only classification was corrected by auditing its input manifest.','', 'Common certificates are assembled from all conjunct windows, not inferred from one pass. Initial K124–129 omitted empty frame clauses and are value-only; K198–203 preserve those clauses. NBP301/302 lack the explicit copy stub and are provisional; use K342/343 with program-base copy controls.','', 'K344 selected caller_ok under a deliberately partial window contract and failed the stronger caller assertion. No positive window proof ran; NCN remains OPEN. L002 and L005 are rejected compilation failures; only L001/L003/L004/L006 supply accepted Lean evidence.', '', 'NEK_LEDGER_DELTA.json contains every baseline receipt plus transitive additions, member-level blockers, exact imported aliases and per-slice row support. NEK_VALIDATION.json is a separate resource/source/receipt audit, not semantic adoption.']
(E/'NEK_RERUNS.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(counts));print(json.dumps(out['receipt_counts']))
