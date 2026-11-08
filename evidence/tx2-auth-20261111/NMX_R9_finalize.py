from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
formal=[r for r in rows if r.get('kind') in ['lean','link','audit','inspect']]
for a in range(1383,1393):
 r=next(r for r in rows if r.get('attempt')=='NMX_L'+str(a) and r.get('kind') in ['lean','audit','inspect'])
 assert r['exit_status']==0,r
 if r['kind']=='lean':assert r['axioms_accepted']
for name in ['NMX_R4_AUDIT_SELECTION.json','NMX_R6_AUDIT_SELECTION.json','NMX_R9_AUDIT_SELECTION.json']:
 d=json.loads((E/name).read_text())
 for m,r in d['modules'].items():
  assert hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()==r['source_sha256'],(name,m)
export=json.loads((E/'NMX_R9_EXPORT.json').read_text());check=json.loads((E/'NMX_R9_RETAINED_CHECK.json').read_text())
assert check['status']=='PASS' and check['checked_export_files']==len(export['files'])>0
assert all(any(r['module']==m for r in export['files']) for m in ['NMX_R4_Authentication','NMX_R6_Validation','NMX_R9_StageTwo','NMX_R9_Native241'])
assert not subprocess.check_output(['git','diff','--name-only','923e04778d3','HEAD','--','crates','programs','Cargo.lock'])
assert not subprocess.check_output(['git','diff','--name-only','--','crates','programs','Cargo.lock'])
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
assert (E/'NMX_ATTEMPTS.jsonl').stat().st_size<20_000_000
counts=dict(prior_formal=766,current_formal=len(formal),resumption_formal=len(formal)-766,formal_ceiling=1066,formal_remaining=1066-len(formal),extraction_prior=6,extraction_total=sum(r.get('kind')=='extract' for r in rows),extraction_resumption=sum(r.get('kind')=='extract' for r in rows)-6,kani_prior=25,kani_total=sum(r.get('kind')=='kani' for r in rows),kani_resumption=sum(r.get('kind')=='kani' for r in rows)-25,attempts_log_bytes=(E/'NMX_ATTEMPTS.jsonl').stat().st_size,stop_reason='All authorized233/242/241 candidates and gates complete; lead ledger review remains. Not a budget stop; no further member proof to attempt, no unchanged regression reruns.',member_by_member={'TX2:233':'Complete candidate/gates; native Box/source and all-Args gaps discharged','TX2:242':'Complete candidate/gates, exact original native tuple, every source observation, Domain=True','TX2:241':'Complete candidate/gates, every242/064 source outcome, all-Args and original D1/D2 only','TX2:217/234':'Already CLOSED by ledger27; unchanged rerun unjustified','other_members':'Outside assigned sequence/prefix scope'},credit='ledger only')
(E/'NMX_RESUMPTION_COUNTS.json').write_text(json.dumps(counts,indent=1)+'\n')
j=json.loads((E/'NMX_R9_PROVENANCE.json').read_text())
for r in j:r['destination_sha256']=hashlib.sha256((E/r['destination']).read_bytes()).hexdigest()
(E/'NMX_R9_PROVENANCE.json').write_text(json.dumps(j,indent=1)+'\n')
p=E/'NMX_R8_SOURCE_GROUP.json';j=json.loads(p.read_text());j.update(status='KERNEL_GROUPING_ACCEPTED; complete candidate in R9, no intermediate raw-error equality claimed',kernel_grouping='NMX_R9_GroupHead241.source',candidate='NMX_R9_StageTwo.root');p.write_text(json.dumps(j,indent=1)+'\n')
p=E/'NMX_HANDOFF.md';p.write_text(p.read_text()+f'''
### Final R9 gates and handoff

Candidate241 commit536c77b6e6b. L1383 final focused combined import PASS18.233583s/6838628KiB/swap0, including the unchanged233/242 candidates, supplied LIB/LIBB gates and complete241 source root. L1384–90 raw ax2 PASS on106 new own theorem roots, groups325–331, exact collector agreement and standard-only axioms. Prior119+73 own roots were not re-audited. Total298 disjoint new own root audits this renewal.

L1391 retention PASS24.651344s/150348KiB/swap0: immutable export NMX_exports_stage241_20261111,18311 loaded modules/34904 objects,745 exported files (85,609,512 bytes). All RSL owners resolve to private revision3; rejected/unloaded artifacts are not exported. L1392 independent retained-file readback PASS0.222571s/45476KiB/swap0:745 files, zero missing/drifted, zero deletions. NMX_R9_VALIDATION.json is current241 gate packet. NMX_R9_SOURCE_AUDIT independently confirms actual reused stage2 source has zero structured loops/bc exits and no control change beyond encoder+immediate map_err grouping. Two immutable Lean COMMENT typos say244 where242 is intended; types/calls/targets are correct (NMX_R9_COMMENT_ERRATA.json), no row244 credit claimed.

Final exact count: {len(formal)} cumulative formal scopes, {len(formal)-766}/300 fresh;2/2 fresh extraction attempts;0/10 fresh Kani (no bc flags), attempts log{counts['attempts_log_bytes']} bytes, below20MB. {1066-len(formal)} fresh formal scopes remain. Completion, not allowance, is the stop reason:233,242 and241 are complete candidates;217/234 already CLOSED; only lead ledger review/credit remains, and no authorized independent member proof remains. No source/trust/key/wallet change or push. Frozen ELF suites not repeated because no covered Rust/cfg/artifact changed. No global security/headline target is established.
''')
print(json.dumps(dict(status='PASS',formal=counts['current_formal'],fresh=counts['resumption_formal'],formal_remaining=counts['formal_remaining'],new_own_roots=298,retained_files=check['checked_export_files'],shipped_changes=0)))
