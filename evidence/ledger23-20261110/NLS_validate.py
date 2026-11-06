"""Independent artifact/ledger/receipt validation; no build or replay."""
from pathlib import Path
import json,lzma,hashlib,collections,re,subprocess,sys
E=Path(__file__).resolve().parent;P=E.parent/'ledger22-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
large=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20000000];assert not large,large
pairs=0
for p in E.rglob('*.xz'):
 q=Path(str(p)[:-3]+'.sha256')
 if not q.exists():continue
 b=lzma.decompress(p.read_bytes());assert H(b)==q.read_text().strip(),str(p);pairs+=1
receipts=[json.loads(l)for l in(E/'NLS_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(receipts)==len({r['attempt']for r in receipts})<=40
library=None;library_checks=0;source_count=0
for r in receipts:
 a=r['attempt'];q=E/a/'receipt.json';rc=J(q);ad=J(E/(a+'-admission.json'));assert rc['attempt']==a and rc['exit_status']==r['exit_status']
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'
 for n,h in rc['source_hashes'].items():assert H(raw(q.parent/'sources'/n))==h,(a,n);source_count+=1
 lib={k:v for k,v in rc['deps_fingerprint']['selected_objects'].items()if'/Aeneas'in k}
 if library is None:library=lib
 assert lib==library,(a,'Aeneas selection changed');library_checks+=1
 assert any(J(p)['free']>=40000000000 for p in E.glob(a+'-disk*.json'))
 if rc['kind']=='lean':assert '-M7000'in rc['command']
rootset=set(J(E/'NLS_AUDIT_ROOTS.json')['roots']);statements=J(E/'NLS_KERNEL_STATEMENTS.json.xz');assert rootset==set(statements)
old=J(P/'NLO_KERNEL_STATEMENTS.json.xz');assert all(statements[k]==v for k,v in old.items())
for p in ['NLS_COMBINED_IMPORT.lean','NLO_COMBINED_IMPORT.lean']:
 lines=(E/p).read_text().splitlines();assert all(not l.strip()or l.startswith('import ')or l=='#print axioms AspisR1.RPx_Deployed.deployed'for l in lines)
assert (E/'NLS_COMBINED_IMPORT.lean').read_bytes()==(E/'NLO_COMBINED_IMPORT.lean').read_bytes()
if '--final'in sys.argv:
 assert len(receipts)==40
 ledger=J(E/'NLO_LEDGER.json.xz');basis=J(P/'NLO_LEDGER.json.xz');by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};delta=J(E/'NLO_LEDGER_DELTA.json')
 assert len(by)==len(oldby)==599
 changed={k for k,r in by.items()if r['status']!=oldby[k]['status']};assert changed=={'TX1:261','TX1:237','TX1:263','TX1:256'}==set(delta['new_closed_rows'])
 assert dict(collections.Counter(r['status']for r in ledger['rows']))=={'CLOSED':580,'OPEN':19}
 assert ledger['trust_rows']==basis['trust_rows']and ledger['Pool_status']==basis['Pool_status']
 assert ledger['extraction_trust_reclassifications']==basis['extraction_trust_reclassifications']
 owners={};rootrefs=0
 for r in ledger['rows']:
  assert r['canonical_callees']==oldby[r['row']]['canonical_callees']
  if r['obligation']!=oldby[r['row']]['obligation']:assert r['obligation_statement_hash']==H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
  for x in r.get('root_owners',[]):
   assert x['root']in statements and statements[x['root']]['owner_module']==x['owner_module'],(r['row'],x)
   if x['root']in owners:assert owners[x['root']]==x['owner_module']
   owners[x['root']]=x['owner_module'];rootrefs+=1
 scan=J(E/'NLO_SCAN.json');assert scan['exit_status']==0 and not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches'])
 audit=J(E/'NLO_AUDIT.json');assert audit['full_composition_pass']and audit['required_roots']==len(rootset)==11302
 assert len(audit['fixtures'])==8 and len(audit['collect_axioms_disagreements'])==2
 results=[x for i in range(30)for x in J(E/f'NLS_audit/batch{i}/proof{i}.json')['results']];assert len(results)==len(rootset)and{r['root']for r in results}==rootset
 assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results)
 root_groups={name:i for i,g in enumerate(J(E/'NLS_AUDIT_ROOTS.json')['groups'])for name in g}
 for r in results:
  p=E/('NLS_NEP_proof'+str(root_groups[r['root']])+'_'+r['root']+'_REACHABLE.txt.xz');assert p.is_file(),r['root']
 physical=J(E/'NLO_PHYSICAL.json');assert set(physical['unowned_open_rows'])=={'TX1:094','TX2:217','TX2:234','TX2:233','TX2:242'}
 assert physical['entry_native_counts']=={'b':{'CLOSED':40,'OPEN':13},'c':{'CLOSED':540,'OPEN':6}}
 assert (E/'NLO_ATTEMPTS.jsonl').read_bytes()==(E/'NLS_ATTEMPTS.jsonl').read_bytes()
 assert J(E/'NLS_FINAL_HOST.json')['status']=='PASS'
 report=dict(status='PASS',scopes=40,sha256_archive_pairs=pairs,source_snapshot_hashes=source_count,library_objects=len(library),library_attempts=library_checks,root_owner_references=rootrefs,canonical_root_owners=len(owners),roots=11302,changed_rows=sorted(changed),shipped_source_changes=0,files_over20MB=0)
 (E/'NLO_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n')
else:report=dict(status='PASS_IN_PROGRESS',scopes=len(receipts),sha256_archive_pairs=pairs,source_snapshot_hashes=source_count,library_objects=len(library),library_attempts=library_checks)
print(json.dumps(report))
