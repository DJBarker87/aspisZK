from pathlib import Path
import json,lzma,hashlib,collections,subprocess
E=Path(__file__).resolve().parent
assert json.loads((E/'NJV_GATE2.json').read_text())['coherence_defects']==0
baseline=E.parent/'ledger15-20261108/NJO_LEDGER.json.xz';raw=lzma.decompress(baseline.read_bytes());ledger=json.loads(raw)
rows={x['row']:x for x in ledger['rows']};selected=['TX2:093','TX1:127'];pairs=[['NJV_K002','NJV_K003']]
P=E.parent/'multiproof3-20261108'
for n in range(13,74):
 p=P/f'NJP_K{n:03d}.json'
 if not p.exists():continue
 x=json.loads(p.read_text());receipt=P/x['attempt']/'receipt.json'
 if not receipt.exists():continue
 r=json.loads(receipt.read_text())
 if r['exit_status']!=0 or n==23 or x['module'] not in {'NJP_sibling_window','NJP_binary_row_window','NJP_digest_write_window','NJP_rejection_prefix','NJP_height_controller','NJP_entry_prefix','NJP_terminal_prefix','NJP_pending_digest_frame','NJP_index_scalar_domain'}:continue
 q=P/f'NJP_K{n+1:03d}.json'
 if q.exists():
  neg=json.loads(q.read_text());nr=P/neg['attempt']/'receipt.json'
  if nr.exists() and json.loads(nr.read_text())['exit_status']==1 and neg['module']==x['module'] and 'NJP_bad_argument' in neg['env'].get('RUSTFLAGS',''):pairs.append([x['attempt'],neg['attempt']])
occurrences=[]
for row in selected:
 r=rows[row];tx=row.split(':')[0];occurrences.append(dict(row=row,returning_root=f'NJV_{tx}.{row.replace(":","_")}',abort_root=f'NJV_{tx}.abort',entry=f'NJV_{tx}Returning.entry',endpoint=f'NJV_{tx}Returning.endpoint',frozen_body_sha256=r['frozen_body_sha256'],baseline_obligation_statement_hash=r['obligation_statement_hash'],original_obligation=r['obligation'],actual_caller='TX2:055' if tx=='TX2' else 'TX1:083',own_domain='Literal deployed Arity Two; original fixed arrays/count/root/node byte slice; input length <=9216. Local cursor zero constructed by ABI. No sortedness/count<=10/acceptance/child-success premise. Larger ABI law includes the preserved unit domain and TX2 <=12.',caller_clauses='NJV_CALLER_INVENTORY.md and verbatim NJV_BASELINE_ROWS.json; no caller row promoted',same_state=True,all_branches=True,gate='NJV_L068/NJV_L069/NJV_L070 PASS; next lead ledger credit pending'))
packet=dict(frozen_revision=ledger['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',functions=[dict(rows=selected,function=rows[selected[0]]['function'],route='(y)/(ai)(5)/(an)/(aq)/(aq)(5)/(au) direct P6 hybrid; native one-step cuts and Lean induction',root_domain='Original binary-entry fixed-array ABI under <=9216 input bytes; generic entry law handles all counts/order by exact rejection. Ten-leaf unit and TX2 twelve-leaf caller clauses retained verbatim, no stronger hidden caller premise.',native_pairs=pairs,lean_roots=['NJV_TX2.TX2_093','NJV_TX2.abort','NJV_TX1.TX1_127','NJV_TX1.abort'],complete_carrier=True,premise_policy='Only SAME original inputs/length and reviewed native parent cuts; child replies installed at SAME arguments; per-cut domains proved as conclusions; no arbitrary Ops, endpoint/child-success/acceptance/Run/exporter premise',trust='P6/D188 option A RECLASSIFICATION; existing Std/runtime/artifact trust retained, none added/removed',occurrences=occurrences)],admission='Both own combined gates PASS; locally gated CLOSED candidates, next authoritative ledger gate required',status='CLOSED candidate packets, not authoritative ledger credit',target_established=False)
(E/'NJV_CLOSED.json').write_text(json.dumps(packet,indent=2)+'\n')
(E/'NJV_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline='evidence/ledger15-20261108/NJO_LEDGER',baseline_sha256=hashlib.sha256(raw).hexdigest(),baseline_counts=dict(closed=463,qualified=0,open=136,total=599),candidate_rows=selected,own_delta_if_admitted=dict(closed=2,qualified=0,open=-2),own_projection_if_admitted=dict(closed=465,qualified=0,open=134,total=599),authoritative_ledger_unchanged=True,credit_pending='next lead ledger gate, no NJP_ candidate double count',occurrences=[dict(row=x['row'],root=x['returning_root'],abort=x['abort_root'],original_obligation_statement_hash=x['baseline_obligation_statement_hash']) for x in occurrences],target_established=False),indent=2)+'\n')
a=[json.loads(l) for l in (E/'NJV_ATTEMPTS.jsonl').read_text().splitlines()];count=collections.Counter(x['kind'] for x in a);metrics=[]
for x in a:
 r=json.loads((E/x['attempt']/'receipt.json').read_text());ad=json.loads((E/(x['attempt']+'-admission.json')).read_text());cfg=json.loads((E/(x['attempt']+'.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert cfg['env']['CARGO_TARGET_DIR'].endswith('/NJV_target')
 metrics.append({k:r.get(k) for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','limits']})
summary=dict(counts=dict(count),kani_used=count['kani'],kani_budget=50,lean_link_audit_used=sum(count[k] for k in ['lean','link','audit']),lean_budget=100,extraction_used=0,prelaunch_failures=['NJV_L006'],unused_reserved_attempt_numbers=list(range(52,60)),metrics=metrics,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),target_established=False)
assert summary['kani_used']<=50 and summary['lean_link_audit_used']<=100
(E/'NJV_RESOURCE_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print('NJV packets prepared: two locally gated candidates; authoritative ledger unchanged; budgets '+str(summary['kani_used'])+'/50 Kani, '+str(summary['lean_link_audit_used'])+'/100 Lean/link/audit')
