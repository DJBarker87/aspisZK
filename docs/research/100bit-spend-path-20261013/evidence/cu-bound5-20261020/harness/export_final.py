"""Export only reviewable evidence, never binaries, proof sidecars or signing keys."""
import json,sys,shutil,hashlib
from pathlib import Path
H=Path(sys.argv[1]);A=H/'analysis';E=H/'export';E.mkdir(exist_ok=True)
read=lambda p:json.loads(p.read_text())
check=read(H/'validation.json');b=read(A/'bound.json')
assert check['unclassified_sites']==0 and check['phase_consistency']['unexplained']==0 and check['sweep_violations']==0
assert b['verdict'] in ['PASS','FAIL']
b.update(target_revision='2318acd430b8474de01e6117248442e3ab0b17b9',candidate_source_revision='c16e59e77a8ee3249d61838b535a6a44ac918caf',
 accepted_splits=[10],admitted_domain_ruling='LEAD-REVIEW-CU-BOUND-3-20261020.md',validation=check,
 verifier_elf_sha256='f9ecbc275b71cf55886351d9445f93e44198d400f7c519573b8f44c9cdb91ae3',
 devnet_elf_sha256='3f21a42fa6376edf68be160894c4be50db1940e13234a99934127dd49a06f851',
 pool_elf_sha256='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548',
 corpus='Exact retained prior grid/random proof corpus, remeasured on candidate ELF; random witnesses and OS masks inherited, not newly sampled',
 label='Analytical argument with executable checks; inherited second-method assumptions, not a formal proof')
(E/'bound.json').write_text(json.dumps(b,indent=1)+'\n')
v=read(A/'variants.json');v.update(verdict=b['verdict'],target_revision=b['target_revision'],accepted_splits=[10]);(E/'variants.json').write_text(json.dumps(v,indent=1)+'\n')
s=read(A/'sites.json');s.update(coverage=check['coverage'],unclassified=[],target_revision=b['target_revision'],new_paths='new-path-audit.json');(E/'sites.json').write_text(json.dumps(s,separators=(',',':'))+'\n')
sets=['control','variants','variants-extra','targeted','random-a','random-b'];lines=[];ledger=[]
for ss in sets:lines+=(H/f'sweep/{ss}/sweep.jsonl').read_text().splitlines()
(E/'sweep.jsonl').write_text('\n'.join(lines)+'\n')
for ss in sets+['trace-main','trace-control','profile']:
 for l in (H/f'sweep/{ss}/ledger.jsonl').read_text().splitlines():
  r=json.loads(l);r.update(target_revision=b['target_revision'],candidate_source_revision=b['candidate_source_revision'],scope_tasks_max=64,print_axioms='N/A: Rust/SBF only');ledger.append(r)
R=E/'receipts';R.mkdir(exist_ok=True);(R/'run-ledger.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in ledger))
for p in (H/'receipts').iterdir():
 if not p.is_dir():continue
 dst=R/'builds'/p.name;dst.mkdir(parents=True,exist_ok=True)
 for n in ['receipt.json','stdout.log','stderr.log','time.log']:
  if (p/n).exists():shutil.copy2(p/n,dst/n)
 if (dst/'receipt.json').exists():
  r=read(dst/'receipt.json');r.update(target_revision=b['target_revision'],candidate_source_revision=b['candidate_source_revision'],scope_tasks_max=64);(dst/'receipt.json').write_text(json.dumps(r,indent=1)+'\n')
for f in ['corpus-inventory.jsonl','validation.json','pins.json','source-validation.json','candidate-source-hashes.json','rule-address-mapping.json','reservation-setup.json','reservation-tracing.json','reservation-analysis.json','trace-inventory.json','artifacts.json','artifacts-sha256.txt','new-path-audit.json','canonical-cap-check.json','canonical-scan-disassembly.txt','package-check.json','harness-inputs.json','definition-audit.json']:
 shutil.copy2(H/f,E/f)
for p in H.glob('reservation-*.json'):shutil.copy2(p,E/p.name)
DA=E/'analysis';DA.mkdir(exist_ok=True)
for f in ['runs.json','residuals.json','profile-phases.json','phase-attribution.json','hash-residuals.json','hash-counts-stage1.json','hash-counts-stage2.json']:
 shutil.copy2(A/f,DA/f)
shutil.copy2(H/'variants-measured.json',DA/'variants-measured.json')
# No obsolete-address conservative calculation is used for the candidate.
# Preserve every per-variant residual as compact text JSON, no binary archive.
spv=read(A/'sites-per-variant.json');compact=[]
for e in spv:
 compact.append(dict(role=e['role'],variant=e['variant'],worst=e['worst'],site_rows=[[x['addr'],x.get('cls'),x['rule'],x['residual'],x.get('count_w',x.get('header_count_w')),x.get('taken_w'),x.get('arms_longest'),x.get('cap',x.get('source_cap_id')),x.get('N')] for x in e['sites']]))
(DA/'sites-per-variant.json').write_text(json.dumps(dict(columns=['elf_addr','class','rule','residual','count_w','taken_w','arms_longest','cap_id','N'],variants=compact),separators=(',',':'))+'\n')
for p in [H/'harness/rules.json',H/'harness/rules-rebased.json']:
 dst=E/'harness'/p.name;dst.parent.mkdir(exist_ok=True);shutil.copy2(p,dst)
P=E/'plans';P.mkdir(exist_ok=True)
for ss in sets+['trace-main','trace-control','profile']:shutil.copy2(H/f'plan-{ss}.json',P/f'plan-{ss}.json')
# Hash raw inputs/CFG data retained on host, instead of exporting huge register or proof data.
retained=[]
for p in sorted(A.glob('*.json')):
 if p.name in ['stage1.json','stage2.json','pool.json','sites-per-variant.json','lines-stage1.json','lines-stage2.json','lines-pool.json']:
  retained.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(E/'retained-analysis.json').write_text(json.dumps(retained,indent=1)+'\n')
print(json.dumps(dict(verdict=b['verdict'],per_kind=b['per_kind'],swept=len(lines),receipts=len(ledger)),indent=1))
