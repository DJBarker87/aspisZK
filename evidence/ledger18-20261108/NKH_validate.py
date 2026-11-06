"""Validate fail-closed reporting and the retained partial gate; no formal replay."""
from pathlib import Path
import json,lzma,hashlib,subprocess,copy
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def read(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def validate(ledger,delta,audit,scan):
 assert ledger==basis
 assert delta['before']==delta['after']=={'CLOSED':514,'QUALIFIED':0,'OPEN':85}
 assert delta['new_count']==0 and delta['new_closed_rows']==[]and delta['rows']==[]
 assert len(set(delta['proposed_rows']))==len(delta['proposed_rows'])==28
 assert delta['gate']=='INCOMPLETE_HOST_HEALTH_STOP'and not delta['trust_rows_changed']
 assert not audit['full_composition_pass']and not audit['all_required_raw_roots_present']and not audit['raw_standard_axioms_only']
 assert audit['required_roots']==10066 and audit['audited_raw_roots']==5367 and len(audit['missing_roots'])==4699
 assert audit['complete_groups']==list(range(16))and audit['missing_groups']==list(range(16,30))
 assert audit['partial_raw_standard_axioms_only']and set(audit['partial_axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert len(audit['fixtures'])==8 and audit['resources']['submitted_scopes']==25 and audit['resources']['complete_receipts']==24
 assert audit['resources']['unused_scopes']==15 and audit['resources']['complete_scope_swaps']==0
 assert scan['exit_status']==0 and scan['modules']==16128 and all(scan[k]==0 for k in ['dangling','incompatible_owners','import_mismatches','canonical_duplicate_owners'])
 assert delta['supplement_status']['status']=='OPEN'and delta['reviewed_transcription_additions']==[]
 assert not ledger['security_target_established']
basis=J(E.parent/'ledger17-20261108/NKC_LEDGER.json.xz');ledger=J(E/'NKH_LEDGER.json.xz');delta=J(E/'NKH_LEDGER_DELTA.json');audit=J(E/'NKH_AUDIT.json');scan=J(E/'NKH_SCAN.json');validate(ledger,delta,audit,scan)
assert (E/'NKH_LEDGER.json.xz').read_bytes()==(E.parent/'ledger17-20261108/NKC_LEDGER.json.xz').read_bytes()
snapshots=0;receipts=0
for p in E.glob('NKH_L[0-9][0-9][0-9]/receipt.json'):
 if not p.stat().st_size:continue
 r=J(p);receipts+=1;ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 for n,h in r['source_hashes'].items():assert H(read(p.parent/'sources'/n))==h,(r['attempt'],n);snapshots+=1
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'and all(k in r for k in ['module','exit_status','wall_seconds','peak_rss_kib','source_revision','deps_fingerprint','print_axioms'])
assert receipts==24
attempts=[json.loads(l)for l in(E/'NKH_ATTEMPTS.jsonl').read_text().splitlines()];assert len(attempts)==25 and len({r['attempt']for r in attempts})==25
last=attempts[-1];assert last['attempt']=='NKH_L025'and last['exit_status']is None and last['wall_seconds']is None and last['peak_rss_kib']is None and last['swaps']is None and last['resubmitted']is False
assert (E/'NKH_L025/receipt.partial.json.txt').stat().st_size==0
compressed=0
for p in E.rglob('*.xz'):
 sha=Path(str(p)[:-3]+'.sha256')
 if sha.exists():assert H(lzma.decompress(p.read_bytes()))==sha.read_text().strip();compressed+=1
assert not any(p.is_file()and(p.stat().st_size>20000000 or p.suffix in ['.olean','.ir','.elf','.o'])for p in E.rglob('*'))
source_paths=['crates','programs','Cargo.lock','docs/research/100bit-spend-path-20261013/crates','docs/research/100bit-spend-path-20261013/programs','docs/research/100bit-spend-path-20261013/Cargo.lock']
assert not subprocess.check_output(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--',*source_paths],cwd=R).strip()
assert not subprocess.check_output(['git','diff','--name-only','HEAD','--',*source_paths],cwd=R).strip()
physical=J(E/'NKH_PHYSICAL.json');assert sum(len(v)for v in physical['open_by_source'].values())==85
assert physical['entry_native_counts']=={'b':{'CLOSED':38,'OPEN':15},'c':{'CLOSED':476,'OPEN':70}}
disposition=J(E/'NKH_SCOPE_DISPOSITION.json');assert len(disposition['unused'])==15 and len(disposition['candidates'])==29
mutations=[]
for label,part,change in [
 ('ledger promotion','ledger',lambda x:next(r for r in x['rows']if r['status']=='OPEN').update(status='CLOSED')),
 ('delta promotion','delta',lambda x:x.update(new_count=1)),
 ('supplement promotion','delta',lambda x:x['supplement_status'].update(status='CLOSED')),
 ('trust addition','delta',lambda x:x['reviewed_transcription_additions'].append({'invented':'trust'})),
 ('gate overclaim','audit',lambda x:x.update(full_composition_pass=True)),
 ('all roots overclaim','audit',lambda x:x.update(all_required_raw_roots_present=True)),
 ('missing root hidden','audit',lambda x:x['missing_roots'].pop()),
 ('bad axioms','audit',lambda x:x.update(partial_axioms=['sorryAx'])),
 ('fixture omitted','audit',lambda x:x['fixtures'].pop()),
 ('wrong scope budget','audit',lambda x:x['resources'].update(submitted_scopes=40)),
 ('duplicate owner','scan',lambda x:x.update(incompatible_owners=1)),
 ('nonzero scan','scan',lambda x:x.update(exit_status=1))]:
 xs=dict(ledger=copy.deepcopy(ledger),delta=copy.deepcopy(delta),audit=copy.deepcopy(audit),scan=copy.deepcopy(scan));change(xs[part])
 try:validate(**xs)
 except AssertionError:mutations.append(label)
 else:raise AssertionError('mutation accepted: '+label)
out=dict(status='PASS_FAIL_CLOSED_REPORTING_ONLY',composition_gate='INCOMPLETE_NO_ADMISSIONS',rows=599,new_rows=0,proposed_rows=28,complete_receipts=receipts,source_snapshots=snapshots,compressed_sha_pairs=compressed,mutation_rejections=mutations,shipped_source_unchanged=True,host_scopes_submitted=25,host_scope_budget=40,no_oversize_or_binary=True)
(E/'NKH_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(validation=out['status'],source_snapshots=snapshots,compressed_sha_pairs=compressed,mutations_rejected=len(mutations))))
