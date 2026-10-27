"""Read-only receipt audit and retention of the requested own Lean cache.

Does not launch compilers, modify shared objects, or charge proof attempts.
"""
import hashlib,json,re,subprocess
from pathlib import Path

root=Path(__file__).resolve().parents[2]
ev=root/'evidence/pv-cb-20261026'
lean=root/'docs/research/v8-r0-zk-20261009/lean'
receipts=[json.loads((ev/f'{i}.json').read_text()) for i in range(27100,27169)]
assert len(receipts)==69 and sum(r['exit']==0 for r in receipts)==66
latest={r['module']:r for r in receipts if r['exit']==0}
# The final audit ran in the last projection group to fit the remaining budget.
# The earlier standalone wrapper is explicitly superseded, never a current result.
superseded=latest.pop('R1Z/PV_CB_CandidateAudit')
for r in latest.values():
    p=lean/(r['module']+'.lean')
    if not p.exists():
        p=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(r['module'].split('/')[-1]+'.lean')
    assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],r['module']
    for a in r['axioms']:
        if 'depends on axioms:' in a:
            assert set(re.findall(r'[\w.]+',re.search(r'\[([^]]*)\]',a)[1])) <= {'propext','Classical.choice','Quot.sound'},a
final=json.loads((ev/'27168.json').read_text())
names={a.split("'")[1] for a in final['axioms']}
assert len(names)==64,len(names)
rows=json.loads((ev/'RESUME-SOURCE-ROWS.json').read_text())
accepted=[r for r in rows if r['status']=='ROW-DISCHARGED(candidate)']
assert len(accepted)==23
for row in accepted:
    assert row['theorem'] in names,row['theorem']
    assert f"R1Z.PV_CB_CandidateDictionary.op{row['op']}" in names
    row['restored_replay_receipt']=str(latest['R1Z/'+row['theorem'].split('.')[-2]]['attempt'])+'.json'
(ev/'RESUME-SOURCE-ROWS.json').write_text(json.dumps(rows,indent=2)+'\n')
probe='''import json,hashlib,shutil
from pathlib import Path
base=Path('/home/dombarker/project-offloads');joint=base/'aspis-joint-20261019';own=base/'codex-pv-cb-20261026'
paths=[str(joint/'objects')]+json.loads((base/'r1-privacy-build-integration-20261019/env/J.json').read_text())['LEAN_PATH'].split(':')
out={};deps={}
for m in MODULES:
 p=joint/'objects'/(m+'.olean');assert p.is_file(),str(p)
 dst=own/'lean-objects'/(m+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 if not dst.exists() or p.read_bytes()!=dst.read_bytes():shutil.copy2(p,dst)
 out[m]={'path':str(dst),'sha256':hashlib.sha256(dst.read_bytes()).hexdigest(),'bytes':dst.stat().st_size,'restored_shared_object':str(p)}
for imp in IMPORTS:
 for folder in paths:
  p=Path(folder)/(imp.replace('.','/')+'.olean')
  if p.is_file():deps[imp]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()};break
 else:raise SystemExit('missing dependency '+imp)
print(json.dumps({'cache':out,'dependencies':deps}))
'''
imports=sorted({imp for r in latest.values() for imp in r['dependency_object_hashes']})
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=probe.replace('MODULES',repr(sorted(latest))).replace('IMPORTS',repr(imports)),text=True))
mismatches=[]
for r in latest.values():
    for imp,sha in r['dependency_object_hashes'].items():
        if sha!=remote['dependencies'][imp]['sha256']:
            mismatches.append({'module':r['module'],'dependency':imp,'receipt_sha':sha,'current':remote['dependencies'][imp]['sha256']})
(ev/'RESUME3-FINAL-CACHE-DEPENDENCIES.json').write_text(json.dumps(dict(
    cache_origin='Own directory survived but own lean-objects did not; initialized from restored aspis-joint objects, now populated with latest successful checked outputs',
    objects=remote['cache'],direct_dependencies=remote['dependencies'],current_dependency_mismatches=mismatches,
    superseded_standalone_wrapper_receipt=superseded['attempt']),indent=2)+'\n')
published=['PV_CB_Op107Source','PV_CB_Op109Source','PV_CB_Op118Source','PV_CB_Op84Source']
for name in published:
    p='docs/research/v8-r0-zk-20261009/lean/R1Z/'+name+'.lean'
    assert (root/p).read_bytes()==subprocess.check_output(['git','show','641d98b783:'+p])
assert not subprocess.check_output(['git','diff','641d98b783','--name-only','--','crates','programs'],text=True).strip()
summary=dict(lean_budget=69,lean_used=69,lean_remaining=0,passed=66,
    failed_attempts=[{k:r[k] for k in ['attempt','module','exit','wall','peak_rss_kib','swap']} for r in receipts if r['exit']!=0],
    kani_used=2,kani_remaining_but_queue_stopped=8,rows_before=18,rows_after=23,endpoint_premises_removed=0,target='not yet established',
    final_audit={**{k:final[k] for k in ['module','exit','wall','peak_rss_kib','swap','source_revision','source_sha256']},
        'receipt':'27168.json','unique_declarations':len(names),'printed_lines_including2_public_repeats':len(final['axioms']),
        'coverage':'23 published source laws,23 joint projections,18 generic/carrier/P6 helpers',
        'axioms':'Only propext, Classical.choice, Quot.sound, or none; no accepted sorryAx',
        'standalone_wrapper':'27135 is the previous22-row audit; final64-declaration commands execute in CandidatePublic at27168; current standalone wrapper generated but not separately recompiled'},
    max_peak_rss_kib=max(r['peak_rss_kib'] for r in receipts),total_swaps=sum(r['swap'] for r in receipts),
    published_prior_interfaces_byte_identical=published,shipped_crates_programs_changes=[],current_dependency_mismatches=mismatches)
(ev/'RESUME3-FINAL-RESULT.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# Resume 3 Lean receipts','','Each row links the complete receipt: exact revision, source SHA, dependency identities and full axioms lines. Standing launcher uses -M7000,6G/8G/swap0/Tasks64. Failed outputs are retained, not accepted.','','|ID|Target|Exit|Wall|Peak RSS KiB|Swap|Revision|Axioms|','|---:|---|---:|---|---:|---:|---|---|']
for r in receipts:
    status='REJECTED failed compile' if r['exit'] else ('standard/none' if r['axioms'] else 'N/A no theorem printed')
    lines.append(f"|[{r['attempt']}]({r['attempt']}.json)|{r['module']}|{r['exit']}|{r['wall']}|{r['peak_rss_kib']}|{r['swap']}|{r['source_revision'][:10]}|{status}|")
(ev/'RESUME3-RECEIPTS.md').write_text('\n'.join(lines)+'\n')
print('69 attempts,66 green,3 failed;64 distinct final audited declarations;',len(mismatches),'current dependency mismatches')
