"""Independent delivery integrity checks and rejecting controls; no proof rerun."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,collections
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):
 if p.suffix=='.xz':
  b=lzma.decompress(p.read_bytes());assert H(b)==Path(str(p)[:-3]+'.sha256').read_text().strip();return json.loads(b)
 return json.loads(raw(p))
ledger=J(E/'NNI_LEDGER.json.xz');old=J(E.parent/'ledger25-20261111/NMQ_LEDGER.json.xz');ob={r['row']:r for r in old['rows']};by={r['row']:r for r in ledger['rows']};review=J(E/'NNI_CANDIDATE_REVIEW.json');audit=J(E/'NNI_AUDIT.json');scan=J(E/'NNI_SCAN.json');required=J(E/'NNI_AUDIT_ROOTS.json');statements=J(E/'NNI_KERNEL_STATEMENTS.json.xz')
def invariants(l,review,audit,scan):
 b={r['row']:r for r in l['rows']};assert len(b)==len(l['rows'])==599 and set(b)==set(ob)
 assert collections.Counter(r['status']for r in l['rows'])=={'CLOSED':583,'OPEN':16}
 assert {id for id in b if b[id]['status']!=ob[id]['status']}=={'TX1:136'}
 assert all(r['canonical_callees']==ob[id]['canonical_callees']for id,r in b.items())
 assert b['TX1:136']['owner_module']=='NNG_Candidate136'and b['TX1:136']['root_owners'][0]['root']=='AspisR1.NNG_Candidate136.candidate'
 assert b['TX2:217']['status']=='OPEN'and review['candidates'][1]['status']=='OPEN_FIDELITY_CONTROL_MISSING'and not review['candidates'][1]['gate_admitted']
 assert review['candidates'][0]['gate_admitted']and review['candidates'][0]['remaining_parameters']==[]
 assert b['TX1:137']['status']=='OPEN'and any(c['id']=='NNI-own:TX1:137:TX1:136:finishInputDom'and c['status']=='OPEN'for c in b['TX1:137']['obligation']['caller_domain_obligations'])
 assert audit['full_composition_pass']and audit['required_roots']==12600 and audit['raw_standard_axioms_only']
 assert set(audit['axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert scan['exit_status']==0 and scan['dangling']==scan['canonical_duplicate_owners']==scan['import_mismatches']==0
 assert {t['id']for t in old['trust_rows']}<={t['id']for t in l['trust_rows']}
 assert l['headline']=='AspisR1.RPx_Deployed.deployed'and l['security_target_established']is False
invariants(ledger,review,audit,scan);controls=[]
for name,which,mutate in [('unproved217_credit','ledger',lambda x:next(r for r in x['rows']if r['row']=='TX2:217').update(status='CLOSED')),('missing_parent_clause','ledger',lambda x:next(r for r in x['rows']if r['row']=='TX1:137')['obligation'].update(caller_domain_obligations=[])),('nonstandard_axiom','audit',lambda x:x.update(axioms=['sorryAx'])),('duplicate_owner','scan',lambda x:x.update(canonical_duplicate_owners=1)),('missing_raw_root','audit',lambda x:x.update(required_roots=12599)),('trust_deletion','ledger',lambda x:x['trust_rows'].pop(0))]:
 args=dict(ledger=ledger,review=review,audit=audit,scan=scan);args[which]=copy.deepcopy(args[which]);mutate(args[which])
 try:invariants(args['ledger'],args['review'],args['audit'],args['scan'])
 except AssertionError:controls.append(dict(control=name,verdict='REJECTED'))
 else:raise AssertionError('Validator accepted '+name)
assert set(statements)==set(required['roots']);references=0
for r in ledger['rows']:
 if r['status']=='CLOSED':
  for ref in r['root_owners']:
   assert ref['root']in statements,(r['row'],ref['root']);references+=1
pairs=0;snapshots=0;pinned_paths={}
for p in E.rglob('*.xz'):
 side=Path(str(p)[:-3]+'.sha256')
 if side.exists():assert H(lzma.decompress(p.read_bytes()))==side.read_text().strip(),str(p);pairs+=1
for p in E.glob('NNI_L*/receipt.json'):
 r=J(p)
 for name,h in r['source_hashes'].items():assert H(raw(p.parent/'sources'/name))==h,(p,name);snapshots+=1
 for name,x in r['deps_fingerprint']['selected_objects'].items():pinned_paths.setdefault(name,set()).add(x['sha256'])
assert all(len(hs)==1 for name,hs in pinned_paths.items()if '/Aeneas' in name)
large=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not large
assert not any(p.name in ['NNI_CLIENT_ACTIVE','NNI_HOLD']for p in E.iterdir())
changed=subprocess.check_output(['git','diff','--name-only','7caae2272ec^','HEAD'],text=True).splitlines();assert all(p.startswith('evidence/ledger26-20261111/NNI_')for p in changed)
r=subprocess.run(['git','diff','--check'],capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
out=dict(status='PASS',rows=599,CLOSED=583,QUALIFIED=0,OPEN=16,required_raw_roots=len(required['roots']),row_root_references=references,compressed_sha_pairs=pairs,source_snapshots=snapshots,selected_Aeneas_paths=sum('/Aeneas'in k for k in pinned_paths),rejecting_controls=controls,all_files_at_most20MB=True,shipped_source='NNI_FROZEN_SOURCE_CHECK.json',no_push=True,no_wallet_or_key_action=True,security_target_established=False)
(E/'NNI_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
