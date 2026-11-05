from pathlib import Path
import json,re,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
receipts=sorted([json.loads(p.read_text()) for p in E.glob('NHV_[KL][0-9][0-9][0-9]/receipt.json')],key=lambda r:r['attempt'])
assert len(receipts)==200 and sum(r['kind']=='kani' for r in receipts)==120
metrics=dict(scopes=len(receipts),kani=120,lean_support=80,extraction=0,extraction_budget=1,wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts))
write('NHV_BUDGET.json',metrics)
results=[];audit_receipts=[]
for i in range(7):
 p=E/'NHV_audit'/('batch'+str(i))/('proof'+str(i)+'.json');x=json.loads(p.read_text());assert x['exit_status']==0
 results+=x['results'];audit_receipts.append(str(p.relative_to(E)))
assert len(results)==127 and len({r['root'] for r in results})==127
for r in results:assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms']) and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
fixture=json.loads((E/'NHV_audit/fixtures/fixtures.json').read_text());assert fixture['exit_status']==0 and len(fixture['results'])==8
scan=[json.loads(x) for x in (E/'NHV_LOADED_scan.jsonl').read_text().splitlines()];summary=dict(exit=0,attempt='NHV_L076',modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan),compatible_replicas=sum(len(r['cached_replicas']) for r in scan));assert not any(summary[k] for k in ['dangling','incompatible_owners','import_mismatches']);write('NHV_SCAN.json',summary)
selected=json.loads((E/'NHV_AUDIT_ROOTS.json').read_text())['selected_modules']
write('NHV_AUDIT.json',dict(status='PASS for selected model/source packets; TX2:065 OPEN',selected=selected,combined='NHV_L063',statement_audit='NHV_L079',root_count=127,roots=results,raw_audit_receipts=audit_receipts,fixtures=dict(attempt='NHV_L068',count=8,same_binary=True),scanner=summary,export='NHV_L077',retained_verification='NHV_L080',source_verification='NHV_L012',standard_axioms=['propext','Classical.choice','Quot.sound'],native_query_raw_rename_stability='OPEN K118 TIMEOUT',native_slot_root_promotions=0))
release=[];native=[]
for r in receipts:
 release.append({k:r[k] for k in ['attempt','kind','module','command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','limits']})
 if r['kind']!='kani':continue
 a=r['attempt'];text=(E/a/'stdout.log').read_text();flags=r['env']['RUSTFLAGS'];timeout='CBMC timed out' in text;compile_fail='Failed to execute cargo' in text
 status='EXCLUDED_TIMEOUT' if timeout else 'EXCLUDED_COMPILE' if compile_fail else 'PASS_LOCAL' if r['exit_status']==0 else 'SEMANTIC_CONTROL_FAIL' if ' --cfg NHV_invert' in flags else 'UNEXPECTED_FAIL'
 if status=='SEMANTIC_CONTROL_FAIL':assert 'VERIFICATION:- FAILED' in text and 'Failed Checks:' in text
 if a in ['NHV_K043','NHV_K044','NHV_K045']:status+='; EXCLUDED_MOVED_RECEIVER_FIXTURE'
 if a in ['NHV_K070','NHV_K071','NHV_K072']:status+='; VALUE_ONLY_SUPERSEDED'
 if a in ['NHV_K004','NHV_K005','NHV_K006']:status+='; EARLY_SHORT_CARRIERS'
 if a=='NHV_K116':status+='; NO_NATIVE_CREDIT_RENAME_TIMEOUT'
 native.append(dict(attempt=a,target=r['module'],status=status,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_sha256=r['source_hashes']['NHV_src/crates/aspis-r1-cost-probe/src/NHV_native.rs'],receipt=a+'/receipt.json'))
write('NHV_RELEASE_RESULTS.json',release);write('NHV_NATIVE_MATRIX.json',dict(attempts=native,root_status='OPEN',quarantined_or_unselected=[dict(positive='NHV_K116',control='NHV_K117',rename='NHV_K118',reason='required rename-stability TIMEOUT90s; no semantic counterexample claimed')],new_composed_rows=0))
# Every source snapshot remains reviewable; fingerprints in full receipts are authoritative.
write('NHV_RESTORE_PATHS.json',['/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHV_exports_20261106']+json.loads((E/'NHV_PATHS.json').read_text())[1:])
status={
'Fresh source transcription/native driver':'PARTIAL; NHV_ReleaseOps.source is the installed MODEL, with P6 transport retained; no whole native driver promotion.',
'Resume full reply':'OPEN NFU producer. K018/019/020 full carriers and all12+4 value facets preserve SAME returned data; do not supply the callee law.',
'Powers native slot':'LOCAL ASSOCIATION READY K031/032/033 + CLOSED NFW; same gamma canonicality remains NFU primitive.',
'Pending and geometry':'MODEL/NATIVE PACKET INPUTS READY: pending one-step/header/full Result and NHV_PendingPacket; NFN geometry same inputs; same width64 producer remains.',
'Query slot':'OPEN raw incoming pending rename stability: K116 PASS, K117 control FAIL, K118 TIMEOUT. Other three argument facets and four output classes pass; SAME NFU domains remain.',
'Flush/writeback':'LOCAL ASSOCIATION READY: shared entry K009/011/013, arbitrary poststate K014/021/022, CLOSED NGC; NHT same-query domain still conditional.',
'Inactive decode':'COHERENT PACKET READY L059 + native K046/047/048; old NET owner conflict resolved by36 import-only replays; full Option/nonreturn.',
'Root/Merkle':'OPEN complete callee/digest-slice law; K049/050/051 covers exact32 root bytes/arguments/full Result only. H VALUE remains runtime trust.',
'Geometry/mark producer installation':'INSTALLED MODEL via NHV_NativeOps and NHV_ReleaseOps, deployed None marker unit; actual parent native closure remains conditional.',
'Finish Prepared/View':'OPEN actual producer S2/canonical fields and same-proof7/7/64 windows. Native K052/053/054 + value/width frames preserve actual slices.',
'Round native slots':'LOCAL ASSOCIATION READY K055–060 with NHE/NHT_RoundOutput; actual primitive Prepared/View domains remain.',
'Dot native slot':'LOCAL ASSOCIATION READY K061–063 with NHE/SAG; actual final_message/post-flush domains remain.',
'NEW':'OPEN NHM_new, exact full Result on same primitive fields; not assumed.',
'Pair':'OPEN NHM_pair / NHT_FinishRelationModel.PairLaw, same NEW weights/alpha/final_message/kappa; not assumed.',
'Finish slot':'OPEN NHM_finish with actual tail domains and above slots; base.op19 explicitly retained.',
'stage2_owned':'NHJ actual native installation remains outside this common-driver job.',
'Carrier/history':'NGS/NGR/TX1/adapter owners; unchanged SDK/read/range/game/persistence premises.'}
original=(E.parents[1]/'evidence/tx2-model2-20261106/NHT_HYPOTHESES.md').read_text();lines=[]
for line in original.splitlines():
 if line.startswith('| Boundary |'):line=line.rstrip()[:-1]+' NHV status / evidence |'
 elif line.startswith('| --- |'):line=line.rstrip()[:-1]+' --- |'
 elif line.startswith('| '):
  boundary=line.split('|')[1].strip();assert boundary in status,boundary;line=line.rstrip()[:-1]+' '+status[boundary]+' |'
 lines.append(line)
(E/'NHV_SLOTS.md').write_text('# NHV exact NHT hypothesis ledger\n\n**TX2:065 OPEN; zero composed-row promotions. Target not yet established.**\n\nThe original NHT statement/owner columns are retained verbatim below. READY\nmeans a packet/input for future composition, never a ledger CLOSED status.\n\n'+'\n'.join(lines)+'\n\nBudgets:120/120 native,80/80 Lean/support,0/1 extraction; reuse fresh NHR by hash.\nRead NHV_REMAINING.md and NHV_FAILING_STEP.md before any continuation.\n')
print(json.dumps(dict(metrics=metrics,scan=summary,roots=len(results))))
