"""Validate completed receipts and emit an OPEN row packet; no implicit promotions."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda n:json.loads((E/n).read_text())
receipts=[read(str(p.relative_to(E))) for p in sorted(E.glob('NJR_[KL][0-9][0-9][0-9]/receipt.json'))]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits and str(r['swaps'])=='0',r['attempt']
 ad=read(r['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True,r['attempt']
 assert r['env']['CARGO_TARGET_DIR'].endswith('/NJR_target')
 assert all(k in r for k in ['source_revision','source_hashes','print_axioms','wall_seconds','peak_rss_kib','exit_status'])
used={'K':sum(r['kind']=='kani' for r in receipts),'L':sum(r['kind']!='kani' for r in receipts),'E':0};assert used==dict(K=55,L=64,E=0),used
attempts=[json.loads(s) for s in (E/'NJR_ATTEMPTS.jsonl').read_text().splitlines()];assert len(attempts)==len(receipts)==len({r['attempt'] for r in attempts})
roots=read('NJR_AUDIT_ROOTS.json')['roots'];raw=[]
for p in sorted((E/'NJR_audit/all').glob('proof*.json')):
 row=json.loads(p.read_text());assert row['exit_status']==0;raw+=row['results']
standard={'propext','Classical.choice','Quot.sound'}
assert set(r['root'] for r in raw)==set(roots) and len(raw)==len(roots)==52
for r in raw:assert r['equal'] and set(r['collect_axioms'])==set(r['walked_axioms'])<=standard,r
fixtures=read('NJR_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and len(fixtures['results'])==8 and all(r['equal'] for r in fixtures['results'])
scan=read('NJR_audit/scan/scan.json');assert scan['exit_status']==0
assert (E/'NJR_audit/scan/scan.log').read_text().strip()=='NFN_SCAN_ZERO_DANGLING'
loaded=[json.loads(s) for s in lzma.decompress((E/'NJR_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()];assert len(loaded)==15721
native=read('NJR_NATIVE_CERTIFICATES.json');assert len(native['rows'])==7 and sum(len(r['controls']) for r in native['rows'])==19
source=read('NJR_SOURCE_VERIFICATION.json');assert not source['source_errors'] and source['lock_unchanged'] and source['closure_modules']==len(loaded)
for a in ['NJR_L058','NJR_L061','NJR_L062','NJR_L063','NJR_L064']:assert read(a+'/receipt.json')['exit_status']==0
baseline=E.parent/'ledger15-20261108/NJO_LEDGER.json.xz';baselineRaw=lzma.decompress(baseline.read_bytes());ledger=json.loads(baselineRaw);assert ledger['counts']['CLOSED']==463 and ledger['counts']['OPEN']==136
before=dict(CLOSED=463,OPEN=136,QUALIFIED=0)
packet=dict(frozen_revision=native['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',functions=[],target='TX2:065',status='OPEN',security_target_established=False,closed_rows=[],closed_edges=[],admitted_rows=[],new_trust_rows=[],local_certificates='NJR_NATIVE_CERTIFICATES.json',model_results='NJR_AUDIT.json',remaining='NJR_REMAINING.md',credit='No promotions; credit waits for the next authoritative ledger gate')
(E/'NJR_CLOSED.json').write_text(json.dumps(packet,indent=2)+'\n')
delta=dict(baseline=str(baseline),baseline_uncompressed_sha256=sha(baselineRaw),before=before,after=before,promotions=[],closed_rows=[],closed_edges=[],target='TX2:065',target_status='OPEN',new_trust_rows=[],gate='component audit only; credit waits for next authoritative ledger gate')
(E/'NJR_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
def brief(a):
 r=read(a+'/receipt.json');return {k:r[k] for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms','cgroup_memory_peak_bytes']}
audit=dict(schema_version=1,status='PASS_COMPONENT_AUDIT_PARENT_OPEN',headline=packet['headline'],target='TX2:065',security_target_established=False,new_closed_rows=0,full_combined_audits=2,second_audit_reason='New independent NJR_WeightFailure.loop/weights source/error induction after the first audit',gate_source_revision=read('NJR_L058/receipt.json')['source_revision'],budget=dict(used=used,limits=dict(K=80,L=100,E=0),under_80_percent_disposition='NJR_REMAINING.md member-by-member, including self-owned unassembled native parent G'),selected_modules=len(read('NJR_MODULES.json')),new_theorems=50,raw_roots=len(raw),raw_axioms=sorted(standard),raw_results=raw,fixtures=fixtures['results'],scan=dict(exit_status=0,modules=len(loaded),summary='NFN_SCAN_ZERO_DANGLING',loaded_manifest='NJR_LOADED_scan.jsonl.xz'),gates=[brief(a) for a in ['NJR_L048','NJR_L052','NJR_L055','NJR_L056','NJR_L058','NJR_L061','NJR_L062','NJR_L063','NJR_L064']],native_components=dict(selected_positive_cuts=7,matched_failing_controls=19,kmx_patch_sha256=native['kmx_patch_sha256'],contract_stubs=False,multiplication_in_kani=False,copy_controls_matched=True),exports=read('NJR_EXPORT.json'),source_verification=source,cleanup=read('NJR_CLEANUP.json'),input_retention=read('NJR_INPUT_RETENTION.json'),closed_packet='NJR_CLOSED.json',ledger_delta='NJR_LEDGER_DELTA.json',scope=dict(no_shipped_file_changes=True,elf_rebuilds=0,elf_hashes='inherited owner pins only; no new ELF claim',no_push=True,no_sibling_worktree_changes=True,no_keys_touched=True,no_new_trust_rows=True),remaining=['M01/full native source-ordered parent G unassembled','M02 merged NJP Merkle CLOSED dependency absent','M06 current-proof Domain activation on every entered finish call not established','all remaining same-invocation uses detailed in NJR_REMAINING.md'])
(E/'NJR_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
# Verify archived inputs after reports are generated; reports are not compiled inputs.
index=read('NJR_INPUT_INDEX.json')
for row in index.values():
 data=(E/row['file']).read_bytes() if 'file' in row else lzma.decompress((E/row['archive']).read_bytes())
 assert len(data)==row['bytes'] and sha(data)==row['sha256'],row
start=subprocess.check_output(['git','rev-parse','deaf9707629^'],text=True).strip()
paths=subprocess.check_output(['git','diff','--name-only',start,'HEAD'],text=True).splitlines();assert all(p.startswith(str(E.relative_to(E.parents[1]))+'/') for p in paths),paths[:3]
assert not list(E.rglob('__pycache__'))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
print(json.dumps(dict(target='TX2:065',status='OPEN',raw_roots=len(raw),scan_modules=len(loaded),native_cuts=7,controls=19,budget=used,receipts_validated=len(receipts))))
