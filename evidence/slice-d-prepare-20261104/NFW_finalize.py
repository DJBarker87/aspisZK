"""Inventory every charged slot; exclude failures instead of turning them into passes."""
from pathlib import Path
import json,hashlib,re,collections,subprocess
E=Path(__file__).resolve().parent
put=lambda n,j:(E/n).write_text(json.dumps(j,indent=1)+'\n')
rows=[]
for i in range(1,101):
 a=f'NFW_K{i:03}';p=E/a/'receipt.json'
 if not p.exists():
  assert i==1,a
  rows.append(dict(attempt=a,role='prelaunch_input_failure',status='EXCLUDED',native_receipt=False,row_credit=False));continue
 r=json.loads(p.read_text());s=(E/a/'stdout.log').read_text();flags=r['env'].get('RUSTFLAGS','');control='NFW_invert' in flags or 'NFW_badarg' in flags or 'wrong' in r['module']
 timeout='timed out' in s.lower() or r['exit_status'] in [124,137]
 status='EXCLUDED_TIMEOUT_OR_KILL' if timeout else 'EXCLUDED_COMPILE_FAILURE' if 'compilation errors' in s or 'could not compile' in s else 'PASS_FRAGMENT' if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s and not control else 'MATCHED_CONTROL_FAILURE' if control and r['exit_status']==1 and 'Failed Checks:' in s else 'UNEXPECTED_RESULT'
 assert status!='UNEXPECTED_RESULT',(a,status,r['exit_status'])
 graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 # Per-stage graph and source/lock checks are preserved in full, not inferred
 # from a representative run. The pinned gate already checked exact equality.
 rows.append(dict(attempt=a,harness=r['module'],role='control' if control else 'positive',status=status,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],native_receipt=True,graph_check=a+'-graph-check.json',lock_check=lock,admission=a+'-admission.json',cgroup=r['cgroup'],limits=r['limits'],row_credit=i in [3,4,5,6,7,8,25,26],interpretation='Fragment only except the eight powers/copy receipts consumed by NFW_certify.py; no caller admission'))
put('NFW_NATIVE_MATRIX.json',dict(roles='Expected failures are controls, not successful native proofs',counts=dict(collections.Counter(r['status'] for r in rows)),attempts=rows,quarantined_function_pointer_passes=[],suspended_static_passes=[],none_observer_families=[[78,79,80],[81,82,83],[84,85,86],[87,88,89],[90,91,92]]))
lean=[]
for i in range(1,71):
 a=f'NFW_L{i:03}';p=E/a/'receipt.json';assert p.exists(),a;r=json.loads(p.read_text());lean.append(dict(attempt=a,kind=r['kind'],target=r['module'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],print_axioms=r['print_axioms'],excluded=bool(r['exit_status']),inspection_only=i in [69,70]))
extract=[]
for i in range(1,4):
 a=f'NFW_E{i:03}';r=json.loads((E/a/'receipt.json').read_text());extract.append(dict(attempt=a,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],scope='partial safe reference descriptor extraction, not a whole shipped-function bridge'))
put('NFW_BUDGET.json',dict(budget=dict(kani=100,lean=70,extraction=3),charged=dict(kani=len(rows),lean=len(lean),extraction=len(extract)),native_host_receipts=sum(r['native_receipt'] for r in rows),native_prelaunch_input_failures=1,lean_support_inspections_included=True,lean=lean,extraction=extract,formal_roots=dict(powers=30,producer_domain=60,memory_io=8,total=98),all_remaining_associations='OPEN; member-by-member in NFW_REMAINING.md'))
base='616c30e35be';changed=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'],text=True).splitlines();assert not changed,changed
put('NFW_FINAL_SOURCE_CHECK.json',dict(base_revision=base,current_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),shipped_crates_programs_changes=changed,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',elf_rebuild_triggered=False,reason='Only NFW evidence/new proof modules and external harness patches; no shipped-file changes',no_push=True,keys_or_wallet_operations=False))
print(json.dumps(dict(native=len(rows),lean=len(lean),extraction=len(extract),native_counts=dict(collections.Counter(r['status'] for r in rows)),raw_roots=98)))
