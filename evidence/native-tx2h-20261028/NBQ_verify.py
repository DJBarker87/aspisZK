from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NBQ_[KL]*/receipt.json'))]
lean=[x for x in receipts if x['kind']=='lean'];kani=[x for x in receipts if x['kind']=='kani']
assert len(kani)==40 and len(lean)<=100
lock=hashlib.sha256(__import__('subprocess').check_output(['git','show','4bb3b3f5:Cargo.lock'])).hexdigest()
for x in kani:
 a=x['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text())
 assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors']
 assert (E/(a+'-lock-after.log')).read_text().strip()==lock
for x in receipts:
 a=x['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
 assert ad['allowed'] is True and x['reservation_retries']>=0
 cfg=json.loads((E/(a+'.json')).read_text())
 assert cfg['reservation_retries']==x['reservation_retries']
 if x['kind']=='lean':assert '-M7000' in cfg['command']
 else:
  assert cfg['env']['CARGO_NET_OFFLINE']=='true'
  assert cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert '--locked' not in cfg['command']
accepted={}
for p in sorted(Path('lean').glob('NBQ_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest();found=[]
 for x in lean:
  snap=E/x['attempt']/'sources'/'NBQ_generated'/p.name
  if x['exit_status']==0 and snap.is_file() and hashlib.sha256(snap.read_bytes()).hexdigest()==sha:found.append(x['attempt'])
 assert found,('no exact passing source',p)
 accepted[str(p)]=dict(sha256=sha,passing_attempts=found)
roots=json.loads((E/'NBQ_AUDIT_ROOTS.json').read_text());audit=next(x for x in lean if x['attempt']=='NBQ_L021')
assert audit['exit_status']==0 and len(audit['print_axioms'])==len(roots)
for line in audit['print_axioms']:
 assert not any(v in line for v in ['sorryAx','axiom ']),line
 if 'depends on axioms:' in line:
  assert set(re.findall(r'\w+',line.split('depends on axioms:',1)[1])) <= {'propext','Classical','choice','Quot','sound'},line
s=dict(lean_attempts=len(lean),lean_passes=sum(x['exit_status']==0 for x in lean),kani_attempts=len(kani),kani_passes=sum(x['exit_status']==0 for x in kani),total_prover_wall_seconds=sum(x['wall_seconds'] for x in receipts),peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),swaps=sum(int(x['swaps']) for x in receipts),all_native_graphs_frozen=True,all_native_locks_unchanged=True,all_admissions_allowed=True,axiom_audit=audit,final_sources=accepted)
(E/'NBQ_VERIFICATION.json').write_text(json.dumps(s,indent=2)+'\n')
print(json.dumps({k:v for k,v in s.items() if k not in ['axiom_audit','final_sources']}))
