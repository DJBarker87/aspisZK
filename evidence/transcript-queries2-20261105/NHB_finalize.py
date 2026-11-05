"""Assemble auditable final metadata; never closes a physical row."""
from pathlib import Path
import json,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda n:json.loads((E/n).read_text())
subprocess.run(['python3',str(E/'NHB_summarize.py')],check=True)
subprocess.run(['python3',str(E/'NHB_validate.py')],check=True)
rs=load('NHB_RESULTS.json');assert rs['counts']==dict(kani=60,lean=28,link=1,audit=5),rs['counts']
proof=[]
for n in ['batch0/proof0','batch1/proof1']:
 p=E/('NHB_audit/'+n+'.json');d=json.loads(p.read_text());assert d['exit_status']==0 and d['swaps']=='0'
 for r in d['results']:
  assert r['equal'] and r['walked_axioms']==r['collect_axioms']
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
 proof+=d['results']
assert {r['root'] for r in proof}==set(sum(load('NHB_AUDIT_ROOTS.json')['groups'],[])) and len(proof)==41
fixtures=load('NHB_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and len(fixtures['results'])==8
expected_fixture_axioms=[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
assert all(r['equal'] and r['collect_axioms']==r['walked_axioms']==expected for r,expected in zip(fixtures['results'],expected_fixture_axioms))
scan=load('NHB_audit/scan/scan.json');assert scan['exit_status']==0
assert 'NFN_SCAN_ZERO_DANGLING' in (E/'NHB_audit/scan/scan.log').read_text()
p=E/'NHB_LOADED_scan.jsonl';assert p.exists()
raw=p.read_bytes();sp=dict(path=p.name,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),rows=len(raw.splitlines()))
if len(raw)>20_000_000:
 q=Path(str(p)+'.xz');q.write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(sp['sha256']+'\n');p.unlink();sp['path']=q.name
# Every target's exact command, exit, wall, RSS, swap, revision, hashes, limits
# and printed axiom output remain in its immutable per-attempt receipt.
summary=dict(root='TX1:168',status='OPEN',composed_rows_added=0,proof_audit='PASS_STANDARD_AXIOMS',proof_roots=proof,headline='AspisR1.RPx_Deployed.deployed',fixtures=dict(status='PASS',count=8,receipt='NHB_audit/fixtures/fixtures.json'),loaded_scan=dict(status='PASS_ZERO_DANGLING',**sp),budget=dict(kani_used=60,kani_limit=60,lean_used=28,support_used=6,lean_and_support_used=34,lean_limit=60,extraction_used=0,extraction_limit=0,remaining_work_requires_native_or_provenance='NHB_REMAINING.md'),results='NHB_RESULTS.json',attempts='NHB_ATTEMPTS.jsonl',native_cases='NHB_MEMBERSHIP_CALLEES.json',native_credit_exclusions=['NHB_K057 positive has timed-out control NHB_K058','all 23 native tool-limit runs','opaque membership Bool K053/K054 has no value credit'],native_association='INCOMPLETE',actual_queries_export=False,shipped_source_changes=False,elf_rebuild='not applicable: no shipped-file changes; inherited pins, not remeasured',inherited_elf_sha256=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',shipping_assumptions='unchanged; local Bool composition uses owner option-A P6/D188 semantic transport reclassification, no trust removal',release_claim=False)
(E/'NHB_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
# Check all receipt fields required by formal-release discipline.
for p in E.glob('NHB_[LK][0-9][0-9][0-9]/receipt.json'):
 r=json.loads(p.read_text())
 for k in ['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms','source_hashes','limits']:assert k in r,(p,k)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
print(json.dumps(dict(root='OPEN',new_roots=40,audited_roots=41,fixtures=8,budget=summary['budget'])))
