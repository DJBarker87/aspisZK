"""Independent receipt/closure/ledger validation. No proof replay."""
from pathlib import Path
import json,lzma,hashlib,collections,copy
E=Path(__file__).resolve().parent;P=E.parent/'ledger23-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
large=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not large,large
pairs=0
for p in E.rglob('*.xz'):
 q=Path(str(p)[:-3]+'.sha256')
 if not q.exists():continue
 b=lzma.decompress(p.read_bytes());assert H(b)==q.read_text().strip(),str(p);pairs+=1
receipts=[json.loads(l)for l in(E/'NLX_ATTEMPTS.jsonl').read_text().splitlines()];assert len(receipts)==len({r['attempt']for r in receipts})==40
library=None;source_count=0
for r in receipts:
 a=r['attempt'];q=E/a/'receipt.json';rc=J(q);ad=J(E/(a+'-admission.json'));assert rc['attempt']==a and rc['exit_status']==r['exit_status']
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and str(rc['swaps'])=='0'
 for n,h in rc['source_hashes'].items():assert H(raw(q.parent/'sources'/n))==h,(a,n);source_count+=1
 lib={k:v for k,v in rc['deps_fingerprint']['selected_objects'].items()if'/Aeneas'in k}
 if library is None:library=lib
 assert lib==library,(a,'Aeneas selection changed')
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 if rc['kind']=='lean':assert '-M7000'in rc['command']
manifest=J(E/'NLX_AUDIT_ROOTS.json');rootset=set(manifest['roots']);statements=J(E/'NLX_KERNEL_STATEMENTS.json.xz');assert rootset==set(statements)
old=J(P/'NLS_KERNEL_STATEMENTS.json.xz');assert all(statements[k]==v for k,v in old.items())
ledger=J(E/'NLX_LEDGER.json.xz');basis=J(P/'NLO_LEDGER.json.xz');delta=J(E/'NLX_LEDGER_DELTA.json');review=J(E/'NLX_CANDIDATE_REVIEW.json')
group_plan=J(E/'NLX_AUDIT_GROUPS.json')['required']
results=[x for a in group_plan for x in J(E/f'NLX_audit/{a["mode"]}/proof{a["group"]}.json')['results']]
def core_check(d,rv,roots,rawresults):
 by={r['row']:r for r in d['rows']};oldby={r['row']:r for r in basis['rows']};assert len(by)==len(oldby)==599
 changed={k for k,r in by.items()if r['status']!=oldby[k]['status']};assert changed=={'TX2:065'}
 assert dict(collections.Counter(r['status']for r in d['rows']))=={'CLOSED':581,'OPEN':18}
 assert by['TX2:064']['status']=='OPEN'and by['TX2:065']['status']=='CLOSED'
 assert by['TX2:065']['root_owners'][0]['root']=='NLT_CompleteRoot.root'
 assert rv['primary_root']=='NLT_CompleteRoot.root'and rv['withdrawn_root_credit']is False and rv['gate_admitted']is True
 assert len(rv['own_argument_clauses'])==3 and rv['cross_transaction_provenance']['established_here']is False
 assert {c['verbatim']for c in rv['own_argument_clauses']}=={'proof.val.length=57607','pub.val.length≤1880','NLP_InputDomain.Root0 ck proof'}
 for x in d['rows']:
  if x['row']not in ['TX2:065','TX2:064']:assert x==oldby[x['row']]
  if x['row']=='TX2:064':assert all(x[k]==v for k,v in oldby[x['row']].items()if k not in ['obligation','obligation_statement_hash'])
  assert x['canonical_callees']==oldby[x['row']]['canonical_callees']
  if x['obligation']!=oldby[x['row']]['obligation']:assert x['obligation_statement_hash']==H(json.dumps(x['obligation'],sort_keys=True,separators=(',',':')).encode())
  for k in x.get('root_owners',[]):assert k['root']in roots and roots[k['root']]['owner_module']==k['owner_module']
 assert len(rawresults)==len(rootset)==11370 and{r['root']for r in rawresults}==rootset
 assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in rawresults)
 return True
assert core_check(ledger,review,statements,results)
# Reject material corruptions of this audit's acceptance conditions.
controls=[]
def reject(name,ld=ledger,rv=review,st=statements,rr=results):
 try:core_check(ld,rv,st,rr)
 except (AssertionError,KeyError):controls.append(dict(name=name,rejected=True));return
 raise AssertionError('mutation accepted '+name)
x=copy.deepcopy(ledger);next(r for r in x['rows']if r['row']=='TX2:064')['status']='CLOSED';reject('unproved parent promotion',ld=x)
x=copy.deepcopy(review);x['primary_root']='NLT_Root.root';reject('withdrawn incomplete root',rv=x)
x=copy.deepcopy(review);x['own_argument_clauses'].pop();reject('omitted original Root0 caller clause',rv=x)
x=copy.deepcopy(statements);x['NLT_CompleteRoot.root']['owner_module']='dangling_owner';reject('noncanonical root owner',st=x)
x=copy.deepcopy(results);x[0]['walked_axioms'].append('forbidden_axiom');reject('nonstandard raw axiom',rr=x)
assert len(controls)==5
assert set(delta['new_closed_rows'])=={'TX2:065'}and not delta['pool_promotions']and not delta['trust_inventory_removals']
assert ledger['trust_rows'][:-1]==basis['trust_rows']and ledger['trust_rows'][-1]['id']=='RuntimeCpiAccountView'and ledger['trust_rows'][-1]['status']=='ADDED-LEAD-20261110'
assert ledger['reviewed_transcription_inventory']==basis['reviewed_transcription_inventory']
assert ledger['open_findings']==basis['open_findings']
assert ledger['Pool_status']==basis['Pool_status']and ledger['extraction_trust_reclassifications']==basis['extraction_trust_reclassifications']
scan=J(E/'NLX_SCAN.json');assert scan['exit_status']==0 and not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches'])
audit=J(E/'NLX_AUDIT.json');assert audit['full_composition_pass']and audit['required_roots']==11370 and len(audit['fixtures'])==8
assert {r['root']for r in audit['collect_axioms_disagreements']}=={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
for entry in group_plan:
 i=entry['group'];g=J(E/'NLX_AUDIT_ROOTS.json')['groups'][i]
 for root in g:assert(E/('NLX_NEP_proof'+str(i)+'_'+root+'_REACHABLE.txt.xz')).is_file(),root
physical=J(E/'NLX_PHYSICAL.json');assert set(physical['unowned_open_rows'])=={'TX2:217','TX2:234','TX2:233','TX2:242'}
assert physical['entry_native_counts']=={'b':{'CLOSED':40,'OPEN':13},'c':{'CLOSED':541,'OPEN':5}}
assert[(x['transaction'],x['open_distance'],x['edges'])for x in physical['shortest_spines']]==[('TX1',6,5),('TX2',5,6)]
assert J(E/'NLX_FINAL_HOST.json')['status']=='PASS'
root_groups={r:g['group']for g in group_plan for r in manifest['groups'][g['group']]}
progress=J(E/'NLX_TIMEOUT_PROGRESS.json');assert progress['replacement_byte_identical_outputs']==319 and not progress['replacement_byte_mismatches']
for row in progress['partial_outputs']:
 group=root_groups[row['root']]
 p=E/('NLX_NEP_proof'+str(group)+'_'+row['root']+'_REACHABLE.txt.sha256');assert p.read_text().strip()==row['sha256']
for p in E.glob('NLX_*.lean'):
 s=p.read_text();assert not any(word in s for word in ['sorry','native_decide','maxRecDepth','maxHeartbeats'])
# Every changed tracked path is confined to the assigned evidence directory.
import subprocess
changed=subprocess.check_output(['git','diff','--name-only',J(E/'NLX_SCOPE.json')['base_revision']],text=True).splitlines();assert all(p.startswith('evidence/ledger24-20261110/')for p in changed)
refs=sum(len(r.get('root_owners',[]))for r in ledger['rows']);owners={z['root']:z['owner_module']for r in ledger['rows']for z in r.get('root_owners',[])}
report=dict(status='PASS',scopes=40,sha256_archive_pairs=pairs,source_snapshot_hashes=source_count,library_objects=len(library),library_attempts=40,root_owner_references=refs,canonical_root_owners=len(owners),roots=11370,changed_rows=['TX2:065'],rejecting_mutations=controls,shipped_source_changes=0,files_over20MB=0,uncompressed_ledger_sha256=H(lzma.decompress((E/'NLX_LEDGER.json.xz').read_bytes())))
(E/'NLX_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n');print('NLX independent validation PASS;40 scopes;5 rejecting mutations;'+str(pairs)+' archive SHA pairs')
