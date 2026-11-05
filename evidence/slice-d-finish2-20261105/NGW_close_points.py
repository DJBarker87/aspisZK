from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
get=lambda n:json.loads((E/n).read_text())
assert get('NGW_L035/receipt.json')['exit_status']==0
scan=[json.loads(l)for l in (E/'NGW_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match']for r in scan)
raw=[json.loads(l[11:])for l in (E/'NGW_L033/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw)
fs=[]
for row,function,pairs in [('TX2:048','state_only_statement_points',list(range(1,17,2))+list(range(25,31,2))),('TX2:047','r0::statement_points',list(range(17,25,2)))]:
 fs.append(dict(function='crates/aspis-core/src/state_only_prefix.rs::'+function,rows=[row],status='CLOSED',form='ruling (y), one source-ordered native iteration, local-record oracle, emitted/reference value association and Lean reverse-loop induction',domain='SAME input array of ten canonical QM31 values; raw returned reply in wrapper; no successful result premise',native_pairs=[[f'NGW_K{i:03d}',f'NGW_K{i+1:03d}']for i in pairs],copy_pair=['NGW_K001','NGW_K002'],lean_root='NGW_PointsPacket.cohort',paired_product_law='NGW_ProductLaw.total',reference='NGW_HelperRef.point_ref; NGW_E001 successful pinned extraction; NGW_PointValue.observed',source_loop_association='NGW_StepModel.iteration; NGW_ReverseInduction.source; NGW_PointsPacket.source',native_source='NGW_ERASURE.json and native-pair exact snapshots',frame='read-only alpha; fixed-array values; native per-word frame lifted by NGW_WordExt; only local successor/carry and oracle log mutate; no allocator, callback or protocol effect',call_domain_derivation='canonical input selects canonical bit; same canonical carry is initialized to ONE and propagated by exact product law and NGW_ConstructorSuccessor.source; exact add/sub outputs and absorption preserve canonicality; wrapper passes SAME alpha',callee_packets=[] if row=='TX2:048'else['TX2:048 (this certificate)'],inner_hypotheses_remaining=[],combined_replay='NGW_L028',ax2='NGW_L033',fixtures='NGW_L034',scan='NGW_L035',axioms=['propext','Classical.choice','Quot.sound'],trust='P6/D188 option A retained/reclassified, not removed; no new trust row'))
closed=get('NGW_CLOSED.json');closed.update(new_composed_functions=2,new_composed_rows=2,functions=fs);(E/'NGW_CLOSED.json').write_text(json.dumps(closed,indent=2)+'\n')
base='../slice-d-finish-20261105/NGM_LEDGER_DELTA.json'
delta=dict(baseline='evidence/ledger8-20261105/NGJ_LEDGER.json.xz',predecessor_delta=base,new_closed_rows=['TX2:047','TX2:048'],new_count=2,rows=[dict(row=f['rows'][0],function=f['function'],before='OPEN',after='CLOSED')for f in fs],no_other_status_change=True,not_a_premise_retirement=True,trust_reclassification='P6/D188 option A retained; no new trust',validator_checks_added=['frozen source shape and exact fission order','matched local-record and copy controls','fresh frozen graph, immutable lock and offline optimized configuration per run','canonical multiplier domain and exact natural-value law','fixed-array per-word frame and extensionality','emitted step and source-loop finite induction','loop-free extracted reference association','same-input wrapper call and child-domain propagation','RPx combined replay','34 standard-only raw ax2 roots','eight same-binary fixtures','13484-module zero-defect NFX scan'])
(E/'NGW_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
(E/'NGW_EDGES.json').write_text(json.dumps(dict(new_closed_edges=[dict(caller=fs[1]['function'],callee=fs[0]['function'],domain='SAME canonical alpha array; unmodified borrowed identity',native_pairs=fs[1]['native_pairs'],lean='NGW_PointsPacket.cohort')],inherited_graph='../slice-d-finish-20261105/NGM_TAIL_GRAPH.json',other_edges='OPEN unless inherited CLOSED'),indent=2)+'\n')
(E/'NGW_AUDIT.json').write_text(json.dumps(dict(status='PASS stage1',combined='NGW_L028',headline='AspisR1.RPx_Deployed.deployed',base='NGK_COMBINED_IMPORT',raw_ax2='NGW_L033',roots=len(raw),standard_only=True,fixtures='NGW_L034 (eight)',scan='NGW_L035',modules=len(scan),defects=0,claim='focused coherent cached replay; not a cold release replay',stages=[dict(stage='statement_points',new_closed_rows=['TX2:047','TX2:048'],combined='NGW_L028',ax2='NGW_L033',scan='NGW_L035')]),indent=2)+'\n')
s=(E/'NGW_TX2_TAIL.md').read_text();a=s.index('## TX2:047');b=s.index('## TX2:127',a)
s=s[:a]+'''## TX2:047 statement_points — CLOSED under (y)

NGW_PointsPacket.cohort, NGW_L028/L033/L035; exact wrapper argument/readonly identity and arbitrary full reply transported by K017..K024, with matched controls; SAME canonical alpha domain discharges the child edge to TX2:048. No parent promotion.

## TX2:048 state_only_statement_points — CLOSED under (y)

K001..K016 and K025..K030: exact source-ordered one-iteration value, product operands/reply, carry, array frame, reverse control, absorption, initialization and record return, all matched controls with exact KMX. E001 extracts the loop-free point reference; NGW_PointValue.observed associates it to emitted arithmetic; NGW_ProductLaw.total supplies the exact canonical natural product; NGW_StepModel.iteration and NGW_ReverseInduction.source prove complete loop association; NGW_PointsPacket.cohort derives full output and canonicality on SAME canonical ten-coordinate input. Combined RPx replay, all 34 new raw roots standard, eight fixtures, scan 13484 modules clean. P6/D188 transport retained.

'''+s[b:]
s=s.replace('NGW has not yet admitted a new CLOSED row.', 'NGW closes TX2:047 and TX2:048 under (y); no acceptance-tail root closes.').replace('full reference/cohort composition and audit are in progress.', 'full statement-point reference/cohort composition and audit pass; polynomial is next.')
(E/'NGW_TX2_TAIL.md').write_text(s)
(E/'NGW_BRIDGES.md').write_text('''# NGW bridge status

TX2:047 statement_points and TX2:048 state_only_statement_points CLOSED under (y). NGW_CLOSED.json gives the exact root domain, native pairs, emitted/reference/loop association, child edge and audit. No caller success, product, allocation or acceptance premise. All four acceptance-tail rows remain OPEN.

Stage1: K001..K030 (15 passing checks,15 matched failures); E001 passes after the diagnosed loop-free reference change; combined L028, raw34 roots L033 standard-only, same-binary8 fixtures L034, L035 scanner13484 modules zero defects. Reused NGM double/guard and product laws are hash-pinned, never rerun. P6/D188 option A and existing trust remain.
''')
with (E/'NGW_HANDOFF.md').open('a')as f:f.write('\n## Stage1 complete\n\nTwo rows CLOSED: TX2:047/048. Native30, extraction1, Lean/audit35 attempts used. Exact certificate NGW_CLOSED.json; combined L028/ax2 L033/fixtures L034/scan L035 all pass (13484 modules). No root/parent promoted. Next: polynomial coefficient-add/reference and complete seven-step source/model association, reusing NGM native observations.\n')
