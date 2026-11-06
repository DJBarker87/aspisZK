"""Finalize only NJF reports from the passing retained receipts."""
from pathlib import Path
import json,hashlib,subprocess,difflib,re
E=Path(__file__).resolve().parent
j=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
v=j(E/'NJF_VALIDATION.json');assert v['status']=='PASS'
audit=j(E/'NJF_L044/audit_outputs/RESULT.json');assert audit['status']=='PASS'
records=[json.loads(x)for x in(E/'NJF_ATTEMPTS.jsonl').read_text().splitlines()];R={r['attempt']:r for r in records}
newpairs=[[p['positive'],p['negative']]for p in v['pairs']]
trust='P6/D188 option A native contract semantic transport RECLASSIFICATION; existing Std/allocator/library/compiler/Aeneas/ABI/source-to-ELF/runtime qualifications retained; no trust row added or removed'
functions=[]
for row,name in [('TX2:129','crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair'),('TX2:115','crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation')]:
 functions.append(dict(rows=[row],function=name,route='(y)(3)/(ai)(5)/(aq)(5) direct hybrid P6',root_domain='Retained SAME-call NIG_FinishInput.Domain proof v p a; reviewed PairPort cut only in the richer root. The nested pair domain is derived at the actual NEW return, never a deployed-root premise.',native_pairs=newpairs,lean_roots=['AspisR1.NJF_Root.finish','AspisR1.NJF_FinishObserved.source','AspisR1.NJF_FinishInstantiation.root']+(['AspisR1.NJF_PairInstantiation.source']if row=='TX2:129'else[]),complete_carrier=True,premise_policy='No RegularProjection/PairWitness/FinishProjection, child success, endpoint equality, invocation ID or physical exporter hypothesis; every child clause discharged at the entered source arguments',trust=trust))
if (E/'NJF_BASELINE_ROWS.json').exists():
 baseline_rows=j(E/'NJF_BASELINE_ROWS.json')
 for f in functions:
  base_row=next(r for r in baseline_rows if r['row']==f['rows'][0] and 'obligation_statement_hash'in r)
  assert base_row['function']==f['function']
  f.update(baseline_original_statement_hash=base_row['obligation_statement_hash'],frozen_body_sha256=base_row['frozen_body_sha256'],original_obligation_policy='All original named/inventory/caller and physical/source-to-ELF qualifications retained; see NJF_BASELINE_ROWS.json, not silently removed')
(E/'NJF_CLOSED.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',headline='AspisR1.RPx_Deployed.deployed',functions=functions,credit_pending_next_ledger_gate=True,authoritative_ledger_promotions=0,target_not_yet_established=True),indent=2)+'\n')
base=E.parent/'ledger13-20261107'
(E/'NJF_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline='evidence/ledger13-20261107/NIU_LEDGER.json',baseline_archive_sha256=sha(base/'NIU_LEDGER.json.xz'),baseline_uncompressed_pin=(base/'NIU_LEDGER.json.sha256').read_text().strip(),baseline_counts=dict(closed=432,qualified=0,open=167,total=599),candidates=[dict(row=x,from_status='OPEN',proposed_status='CLOSED',gate='NJF_L044',credit_pending_next_ledger_gate=True)for x in ['TX2:129','TX2:115']],authoritative_promotions=0,prospective_counts_if_admitted=dict(closed=434,qualified=0,open=165,total=599)),indent=2)+'\n')
(E/'NJF_AUDIT.json').write_text(json.dumps(dict(status='PASS',combined_import='NJF_COMBINED_IMPORT',mandatory_imports=['NGK_COMBINED_IMPORT','NIU_COMBINED_IMPORT','NIW_COMBINED_IMPORT'],headline='AspisR1.RPx_Deployed.deployed',complete_audits_used=2,maximum_complete_audits=2,final_attempt='NJF_L044',final_receipt={k:R['NJF_L044'][k]for k in ['source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','limits','source_hashes','deps_fingerprint']},result=audit,print_axioms_result={r['root']:r['walked_axioms']for r in [json.loads(line[11:])for line in (E/'NJF_L044/audit_outputs/raw.log').read_text().splitlines()if line.startswith('NEP_RESULT ')]},fixtures='NJF_L037: eight identities equal NIW_L027 with the SAME new proof binary used for final raw audit',historical_attempt='NJF_L041:221 roots/15194 modules; full stdout and resource receipt retained; final per-module snapshot supersedes its common-path scan file',raw_scope='Every new theorem plus all NIW source roots and headline (224 roots) in the full combined environment; NIU 8182-root prior audit reused for unchanged inherited row roots',trust=trust,release_replay=False),indent=2)+'\n')
# Scratch patch is relative to the committed NIG frozen repair-input capsule.
import runpy
prepared=runpy.run_path(str(E/'NJF_native_prepare.py'))['inputs'];old=j(E.parent/'slice-d-pair4-20261107/NIG_BASE_REPAIR_INPUTS.json')
patch=''
for name,text in prepared.items():
 before=old.get(name,'');patch+=''.join(difflib.unified_diff(before.splitlines(True),text.splitlines(True),fromfile=('a/'+name if name in old else '/dev/null'),tofile='b/'+name))
(E/'NJF_gap_cuts.patch').write_text(patch)
# Exact printed kernel statements, retaining the source-helper/deployed-root distinction.
statements={}
for attempt in ['NJF_L018','NJF_L022','NJF_L028']:
 text=(E/attempt/'stdout.log').read_text()
 for name in ['AspisR1.NJF_PairInstantiation.root','AspisR1.NJF_Root.finish']:
  m=re.search(r'theorem '+re.escape(name)+r' : (.*?) :=\n',text,re.S)
  if m:statements[name]=dict(statement=m.group(1),receipt=attempt,kind='internal source helper; primitive pair domain discharged in FinishObserved.source'if 'PairInstantiation' in name else'deployed pair-and-finish positive hybrid certificate root')
assert len(statements)==2
(E/'NJF_STATEMENTS.json').write_text(json.dumps(statements,indent=2)+'\n')
(E/'NJF_HYPOTHESIS_AUDIT.md').write_text('''# Root hypothesis audit

The deployed pair/finish root is `AspisR1.NJF_Root.finish`, printed in L022/L028 and raw-audited in L044. Its pair conjunct is the SAME actual nested pair certificate, not an independently selected packet. `NJF_FinishInstantiation.root` is the result-only finish root with just the retained Domain.

| Root input | (aq)(2) inventory |
|---|---|
| r, loc, proof, v, p, a, port, afterOwner | Data/actual-call parameters |
| NIG_FinishInput.Domain proof v p a | Retained SAME-call NHV/NID caller predicate; not closed here |
| NIW_AlignFinishPort.Cut specialized to (NJF_FinishObserved.G ...).info | Reviewed (ai)(5) parent PairPort transcription, at the actual complete collected pair Result; no returning cut on fail/div or unentered pair |

`NJF_PairInstantiation.root` is an INTERNAL source helper on primitive NIT_PairDomain.Domain, not a standalone admissible deployed row root. The domain is discharged inside NJF_FinishObserved.source/detail_source and NJF_FinishInstantiation.source using NIT_PairDomain.caller at the SAME actual NEW success, introduced by internal Result case analysis. The positive deployed pair certificate is the Bound conjunct of NJF_Root.finish, which has only the inventory above. No primitive pair domain is added to that root.

All powers, regular/common/partial/high/tail and full mutable post clauses are produced internally from CLOSED child calls at their logged decoded arguments. No child Result equation/success, whole endpoint, RegularProjection, PairWitness, FinishProjection, physical exporter, invocation-ID or equal-address-implies-payload field is a root premise. L028 prints the hidden Domain and reviewed Cut. NJF_STATEMENTS.json preserves the exact statements. Only standard axioms occur in the final compiled sources and raw closure.
''')
# Resource / freeze synopsis is evidence, not a fresh artifact build.
trees=subprocess.check_output(['git','rev-parse','HEAD:crates','HEAD:programs'],text=True).splitlines()
assert trees==['9c52e6b936c8c774c1238973f4acd47460c4afba','ebd375c65012fb140dfc5988b0d013694b03bab5']
frozen=j(E/'NJF_FROZEN.json');frozen['final_crates_tree']=trees[0];frozen['final_programs_tree']=trees[1];frozen['shipped_source_changed']=False;frozen['elf_rebuild_triggered']=False;(E/'NJF_FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
print(json.dumps(dict(candidates=2,authoritative_promotions=0,root_hypotheses='inventory only',raw_roots=audit['roots'],scan_modules=audit['modules'],shipped_trees_unchanged=True)))
