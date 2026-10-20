"""Freeze evidence after completed sweep and independent validation.
Usage: finalize.py host-root
"""
import json,sys,collections,shutil
from pathlib import Path
H=Path(sys.argv[1]);A=H/'analysis';E=H/'export';E.mkdir(exist_ok=True)
checks=json.loads((H/'validation.json').read_text());b=json.loads((A/'bound.json').read_text())
b['inequality_checks']='PASS' if all(x['B_stage1']<=1300000 and x['B_settlement']<=1300000 for x in b['per_kind'].values()) else 'FAIL'
b['verdict']='FAIL' if b['inequality_checks']=='FAIL' else 'INCOMPLETE'
b['incomplete_requirements']=['Literal steps 1/7 request accepted runs for splits 10 and 11; adopted candidate.rs:193 rejects k != SPLIT=10. Both kinds reject split11 with InvalidInstructionData. No accepted split11 sample or measured worst input exists. Criteria are not waived.']
b['accepted_splits']=[10];b['rejected_split11']={'source':'crates/aspis-r1-cost-probe/src/candidate.rs:193-195; compact.rs:28','accepted_runs':0,'kinds_tested':['transfer','withdrawal'],'result':'Parse / InvalidInstructionData'}
b['bit_reversed_target']={'scope':'actual multiproof component, not forced complete Fiat-Shamir transaction','global_distinct_queries':22,'slot_nodes':[146,146,128,172,172,150],'total_nodes':914,'verified_components':4,'wrong_sibling_rejections':4}
b['target_revision']='e90cf2f800f7177e5cca47aa7e5ba59a940130dd';b['validation']=checks
(A/'bound.json').write_text(json.dumps(b,indent=1)+'\n')
# Propagate conservative campaign status and source-level SHA terms to all deliverables.
v=json.loads((A/'variants.json').read_text());v.update(verdict=b['verdict'],inequality_checks=b['inequality_checks'],target_revision=b['target_revision'])
v['excluded_variants']=[dict(kind=k,split=11,accepted_runs=0,B=None,reason='Empty accepted domain; candidate.rs:193-195 requires split10; two executable rejection checks in receipts/run-ledger.jsonl') for k in ['transfer','withdrawal']]
(A/'variants.json').write_text(json.dumps(v,indent=1)+'\n')
s=json.loads((A/'sites.json').read_text());s['coverage']=checks['coverage'];s['unclassified']=[];s['target_revision']=b['target_revision'];(A/'sites.json').write_text(json.dumps(s,separators=(',',':'))+'\n')
for f in ['bound.json','variants.json','sites.json']:shutil.copy2(A/f,E/f)
sets=['control','fresh-control','variants','variants-extra','targeted','random-a','random-b']
rows=[json.loads(l) for ss in sets for l in (H/'sweep'/ss/'sweep.jsonl').read_text().splitlines()]
(E/'sweep.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
R=E/'receipts';R.mkdir(exist_ok=True)
ledger=[]
for ss in sets+['trace-main','trace-control','profile','split11-rejection']:
 for l in (H/'sweep'/ss/'ledger.jsonl').read_text().splitlines():
  r=json.loads(l);r.update(target_revision=b['target_revision'],print_axioms='N/A: Rust/SBF only',artifact_pins='../artifacts-sha256.txt',scope_tasks_max=64);ledger.append(r)
(R/'run-ledger.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in ledger))
for p in (H/'receipts').iterdir():
 if p.is_dir():shutil.copytree(p,R/'builds'/p.name,dirs_exist_ok=True)
for f in ['trace-main-initial.log','rule-address-mapping.json','source-validation.json','validation.json','target-selection.json','reservation-tracing.json','reservation-analysis.json','trace-inventory.json','artifacts.json','artifacts-sha256.txt']:
 if (H/f).exists():shutil.copy2(H/f,E/f)
DA=E/'analysis';DA.mkdir(exist_ok=True)
for f in ['runs.json','residuals.json','profile-phases.json','phase-attribution.json','hash-residuals.json','hash-counts-stage1.json','hash-counts-stage2.json']:
 shutil.copy2(A/f,DA/f)
shutil.copy2(H/'variants-measured.json',DA/'variants-measured.json')
# Both executable split-11 counterexamples retain complete diagnostics, no key files.
for rdir in (H/'sweep/split11-rejection/runs').iterdir():
 dst=R/'split11-rejection'/rdir.name;dst.mkdir(parents=True,exist_ok=True)
 for name in ['stderr.log','stdout.log','time.log']:shutil.copy2(rdir/name,dst/name)
# Fresh-control native acceptance, node counts, proof hashes and equal-public assertion.
fresh=[]
for rd in sorted((H/'sweep/fresh-control/runs').iterdir()):
 lines=(rd/'stderr.log').read_text().splitlines();native=json.loads(next(l.split('=',1)[1] for l in lines if l.startswith('FORMAT_ADOPT_NATIVE=')))
 fresh.append(dict(label=rd.name,native=native,public_equal_saved=any(l.startswith('PROOF_SIZE_PUBLIC_MATCHES=') for l in lines)))
(DA/'fresh-controls.json').write_text(json.dumps(fresh,indent=1)+'\n')
print(json.dumps(dict(verdict=b['verdict'],inequality_checks=b['inequality_checks'],swept=len(rows),run_receipts=len(ledger),per_kind=b['per_kind']),indent=1))
