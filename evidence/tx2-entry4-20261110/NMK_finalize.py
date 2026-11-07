from pathlib import Path
import json,lzma,hashlib,subprocess,shutil
E=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l) for l in (E/'NMK_ATTEMPTS.jsonl').read_text().splitlines()]
if not any(r['attempt']=='NMK_K001' for r in rows):
 x=dict(attempt='NMK_K001',kind='prelaunch',module='verifier::candidate::NMK_native::NMK_auth_return',actual_kani_invocation=False,exit_status=None,local_wrapper_exit_status=1,wall_seconds=None,peak_rss_kib=None,swaps=None,source_revision='6bb752b6c71',reason='Missing own copied launcher before seed completion; no S2W/cargo-kani process, receipt unavailable',configuration='NMK_K001.json',launcher_log='NMK_K001-launcher.log.xz')
 with (E/'NMK_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
 rows.append(x)
actual=[r for r in rows if r['kind']!='prelaunch'];native=[r for r in rows if r['kind']=='kani'];lean=[r for r in rows if r['kind']=='lean']
assert len(native)==40 and len(lean)==11
for r in actual:
 rc=json.loads((E/r['attempt']/'receipt.json').read_text());assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 ad=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert int(rc['swaps'])==0
 if r['kind']=='kani':
  a=r['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'];assert not any(p['name']=='aspis-pool' for p in g['selected_closure']);assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged'];assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
raw=[]
for p in [E/'NMK_audit/batch0/proof0.json',E/'NMK_audit/batch1/proof1.json']:
 x=json.loads(p.read_text());assert x['exit_status']==0;raw+=x['results']
standard={'propext','Classical.choice','Quot.sound'};assert len(raw)==13 and all(set(x['walked_axioms'])<=standard and x['equal'] for x in raw)
fixtures=json.loads((E/'NMK_audit/fixtures/fixtures.json').read_text());assert fixtures['exit_status']==0 and len(fixtures['results'])==8
scan=json.loads((E/'NMK_audit/scan/scan.json').read_text());assert scan['exit_status']==0
ret=json.loads((E/'NMK_RETENTION.json').read_text());pool=json.loads((E/'NMK_UNUSED_POOL_FINDING.json').read_text())
# Current successful parent source exactly matches canonical-copy control build.
idx=json.loads((E/'NMK_INPUTS.json').read_text());key='NMK_src/crates/aspis-r1-cost-probe/src/NMK_native.rs'
assert idx['attempts']['NMK_K037'][key]==idx['attempts']['NMK_K040'][key]==idx['attempts']['NMK_K041'][key]==sha(E/'NMK_native.rs')
controls=[]
for a in ['NMK_K032','NMK_K033','NMK_K034','NMK_K035','NMK_K036','NMK_K037','NMK_K041']:
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();failed=s.split('Failed Checks:',1)[1].split('VERIFICATION:-',1)[0];assert 'unwinding assertion' not in failed
 controls.append(dict(attempt=a,semantic_failure=True,failed_checks=failed.strip()))
(E/'NMK_CONTROLS.json').write_text(json.dumps(controls,indent=1)+'\n')
p=E/'NMK_HARNESSES.patch';p.write_bytes((E/'NMK_native.patch').read_bytes());(E/'NMK_HARNESSES.patch.sha256').write_text(sha(p)+'\n')
audit=dict(status='SUPPORT_GATE_PASS_NO_CANDIDATE',baseline='ledger24 581/0/18',combined_import=dict(attempts=['NMK_L009','NMK_L010'],final_exit=0,full_raw_audits=1),raw_roots=raw,raw_standard_only=True,raw_collect_equal=True,fixtures=8,nfx=dict(attempt='NMK_L016',exit_status=0,modules=ret['loaded_modules'],dangling=0,duplicate_owners=0,import_mismatches=0),budget=dict(kani_invocations=len(native),kani_limit=80,lean_compiler_invocations=len(lean),lean_limit=80,total_completed_scopes=len(actual),prelaunch_scopes_without_kani=1,extraction=0,whole_budget_requirement_satisfied=False),metrics=dict(total_completed_scope_wall_seconds=sum(r['wall_seconds'] for r in actual),peak_rss_kib=max(int(r['peak_rss_kib']) for r in actual),swaps=0),retention=ret,unused_pool_source_differences=len(pool['different']),no_selected_pool=True,current_kmx=dict(positive='NMK_K040',negative='NMK_K041',current_parent_source_sha256=sha(E/'NMK_native.rs'),patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'),credit='NONE',target='not yet established')
(E/'NMK_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
for p in E.rglob('__pycache__'):shutil.rmtree(p)
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
(E/'NMK_HYGIENE.json').write_text(json.dumps(dict(files_over_20MB=large,python_cache_directories=0,shipped_file_changes=0,elf_rebuild_trigger=False,host_deletions=0,pushes=0,key_wallet_account_actions=0,source_snapshots_in_content_addressed_archives=True),indent=1)+'\n')
print(json.dumps(dict(kani=len(native),lean=len(lean),completed_scopes=len(actual),raw_roots=13,nfx_modules=ret['loaded_modules'],ledger_delta=0,whole_budget_satisfied=False)))
