"""Summarize actual receipts; no ledger row promotion or inferred native credit."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent
base=E.parent/'ledger20-20261109/NKW_LEDGER.json.xz';raw=lzma.decompress(base.read_bytes());counts=dict(CLOSED=560,QUALIFIED=0,OPEN=39)
rows={n:'OPEN'for n in ['TX1:328','TX1:345','TX1:344','TX1:333','TX1:330']}
x=dict(baseline=str(base.relative_to(E.parent.parent)),baseline_counts=counts,headline='AspisR1.RPx_Deployed.deployed',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',rows=rows,closed=[],complete_native_parents=[],complete_parameterized_folds=[],composed_roots=[],candidates=[],authoritative_credit=False,security_target_established=False,status='INCOMPLETE; target not yet established')
(E/'NLD_CLOSED.json').write_text(json.dumps(x,indent=1)+'\n')
delta=dict(basis=x['baseline'],basis_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),basis_uncompressed_sha256=hashlib.sha256(raw).hexdigest(),before=counts,after=counts,promotions=[],added_edges=[],removed_edges=[],explicit_parent_clause_updates=[],owned_rows=rows,candidate_roots=[],security_target_established=False,status='NO_COMPOSED_ROW_CREDIT')
(E/'NLD_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
attempts=[json.loads(l)for l in(E/'NLD_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(attempts)==len({x['attempt']for x in attempts})
for r in attempts:
 f=E/r['full_receipt'];receipt=json.loads(f.read_text())
 assert receipt['exit_status']==r['exit_status']
 for rel,h in receipt['source_hashes'].items():
  p=f.parent/'sources'/rel;assert hashlib.sha256(p.read_bytes()).hexdigest()==h,str(p)
 assert receipt['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-tx1-entry-20261109/NLD_target'
 assert int(receipt['swaps'])==0
 admission=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed']is True
 assert json.loads((E/(r['attempt']+'-disk-0.json')).read_text())['free']>=40_000_000_000
scanpath=E/'NLD_LOADED_scan.jsonl';scan=None
if scanpath.exists():
 scans=[json.loads(l)for l in scanpath.read_text().splitlines()];scan=dict(modules=len(scans),dangling=sum(len(x['dangling'])for x in scans),incompatible_owners=sum(len(x.get('duplicate_owners',[]))for x in scans),import_mismatches=sum(not x['imports_match']for x in scans),declarations=sum(x['declarations']for x in scans),references=sum(x['edges']for x in scans))
 scan['exit_status']=0 if not any(scan[k]for k in ['dangling','incompatible_owners','import_mismatches'])else 1
(E/'NLD_SCAN.json').write_text(json.dumps(scan,indent=1)+'\n')
audit=dict(status='SOURCE_SUPPORT_ONLY; target not yet established',kani_used=0,kani_allowance=30,formal_scopes_used=len(attempts),lean_allowance=130,extractions_used=0,extraction_allowance=0,successful_scopes=sum(r['exit_status']==0 for r in attempts),failed_drafts=[r['attempt']for r in attempts if r['exit_status']!=0],wall_seconds=sum(r['wall_seconds']for r in attempts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in attempts),swaps=0,full_combined_import_compiles=2,source_folds=['first_decoded','stage1_owned','process','entry'],complete_native_folds=0,complete_parameterized_folds=0,scan=scan,raw_axiom_results=[],native_credit=False,budget_exhausted=False,early_return_explanation='NLD_REMAINING.md; incomplete work, not a claim that unspent budget proves impossibility')
for p in sorted((E/'NLD_audit').glob('*/*.json')):
 r=json.loads(p.read_text());audit['raw_axiom_results'].append(dict(path=str(p.relative_to(E)),exit_status=r['exit_status'],roots=len(r.get('results',[]))))
proof=json.loads((E/'NLD_audit/batch0/proof0.json').read_text())
standard={'propext','Classical.choice','Quot.sound'}
assert proof['exit_status']==0 and len(proof['results'])==29
assert all(r['equal']is True and set(r['walked_axioms'])<=standard and set(r['collect_axioms'])<=standard for r in proof['results'])
fixtures=json.loads((E/'NLD_audit/fixtures/fixtures.json').read_text())
assert fixtures['exit_status']==0 and len(fixtures['results'])==8
assert scan['exit_status']==0
audit.update(raw_ax2_standard=True,raw_roots=29,mutation_fixtures=8,hypothesis_inventory='NLD_HYPOTHESIS_INVENTORY.json',statements='NLD_L029/stdout.log',retained_export='NLD_EXPORT.json')
(E/'NLD_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
frozen=subprocess.run(['git','diff','--exit-code','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates/','programs/r1-cost-probe/','Cargo.lock'],capture_output=True)
assert frozen.returncode==0
(E/'NLD_FROZEN_SOURCE_CHECK.json').write_text(json.dumps(dict(command=frozen.args,exit_status=frozen.returncode,stdout_sha256=hashlib.sha256(frozen.stdout).hexdigest(),shipped_source_changed=False,elf_rebuild_trigger=False),indent=1)+'\n')
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*')if p.is_file())
assert not list(E.rglob('__pycache__'))
subprocess.run(['python3',str(E/'NLD_generate_stage1.py'),'--check'],check=True)
subprocess.run(['git','diff','--check'],check=True)
print(json.dumps(dict(scopes=len(attempts),native_credit=False,scan=scan)))
