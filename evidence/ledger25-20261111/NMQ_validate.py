"""Independent final artifact/receipt integrity, including rejection controls."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;P=E.parent/'ledger24-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):
 if p.suffix=='.xz':
  b=lzma.decompress(p.read_bytes());assert H(b)==Path(str(p)[:-3]+'.sha256').read_text().strip();return json.loads(b)
 return json.loads(raw(p))
def check(ledger,audit,scan,basis):
 assert audit['full_composition_pass']and audit['raw_standard_axioms_only']and audit['all_required_raw_roots_present']
 assert audit['same_optimized_proof_binary_sha256']==J(P/'NLX_AUDIT.json')['same_optimized_proof_binary_sha256']
 assert set(audit['axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert scan['exit_status']==0 and not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches'])
 by={r['row']:r for r in ledger['rows']};old={r['row']:r for r in basis['rows']};assert len(by)==len(old)==599
 assert [r for r in by if by[r]['status']!=old[r]['status']]==['TX2:064']
 assert all(by[r]['canonical_callees']==old[r]['canonical_callees']for r in by)
 assert by['TX2:241']['status']=='OPEN'and by['TX2:064']['owner_module']=='NMN_064'
 assert [r['root']for r in by['TX2:064']['root_owners']]==['NMN_064.root']
 clauses=by['TX2:241']['obligation']['NMQ_explicit_child_domains']['clauses'];assert len(clauses)==4
 assert {c['predicate']for c in clauses}=={'proof.val.length = 57607','checkpoint.val.length = 1768','publicBytes.val.length ≤ 1880','NLP_InputDomain.Root0 checkpoint proof'}
 rt=by['TX2:064']['obligation']['NMQ_root0_decision'];assert rt['same_occurrence']and rt['no_new_trust']and rt['no_global_root0']and rt['no_hash_injectivity']
 assert rt['headline_theorem']=='NMF_GameRoot.root0_or_existing_collision'and rt['event']=='unchanged Q0+Q1+2965 event and same program/projection/selector'
 oldtrust={r['id']:r for r in basis['trust_rows']};newtrust={r['id']:r for r in ledger['trust_rows']}
 for id,r in oldtrust.items():
  n=copy.deepcopy(newtrust[id])
  if id=='NativeContractSemanticTransport':n['direct_closed_rows'].remove('TX2:064')
  assert n==r,id
 assert not ledger['security_target_established']and ledger['frozen_revision']==basis['frozen_revision']and ledger['pins']==basis['pins']
def main():
 ledger=J(E/'NMQ_LEDGER.json.xz');basis=J(P/'NLX_LEDGER.json.xz');audit=J(E/'NMQ_AUDIT.json');scan=J(E/'NMQ_SCAN.json');check(ledger,audit,scan,basis)
 mutants=[]
 for name,fn in [('missing_gate',lambda l,a,s:a.update(full_composition_pass=False)),('wrong_binary',lambda l,a,s:a.update(same_optimized_proof_binary_sha256='0'*64)),('unexpected_axiom',lambda l,a,s:a['axioms'].append('bad')),('duplicate_owner',lambda l,a,s:s.update(canonical_duplicate_owners=1)),('missing_caller_clause',lambda l,a,s:next(r for r in l['rows']if r['row']=='TX2:241')['obligation']['NMQ_explicit_child_domains']['clauses'].pop()),('changed_event',lambda l,a,s:next(r for r in l['rows']if r['row']=='TX2:064')['obligation']['NMQ_root0_decision'].update(event='new collision event'))]:
  l,a,s=copy.deepcopy((ledger,audit,scan));fn(l,a,s)
  try:check(l,a,s,basis)
  except AssertionError:mutants.append(dict(name=name,rejected=True));continue
  raise AssertionError('accepted mutant '+name)
 archives=0;snapshots=0;receipts=[];aeneas={}
 for p in E.rglob('*.xz'):
  b=lzma.decompress(p.read_bytes());side=Path(str(p)[:-3]+'.sha256')
  assert side.exists()and side.read_text().strip()==H(b),str(p);archives+=1
 for q in E.glob('NMQ_L[0-9][0-9][0-9]/receipt.json'):
  r=J(q);receipts.append(r)
  for n,h in r['source_hashes'].items():assert H(raw(q.parent/'sources'/n))==h;snapshots+=1
  pins={k:v for k,v in r['deps_fingerprint']['selected_objects'].items()if '/Aeneas/'in k or '/AeneasMeta/'in k or Path(k).name.startswith(('Aeneas.','AeneasMeta.'))}
  for k,v in pins.items():
   if k in aeneas:assert aeneas[k]==v['sha256']
   aeneas[k]=v['sha256']
 assert len(receipts)==40
 statements=J(E/'NMQ_KERNEL_STATEMENTS.json.xz');refs=[v for r in ledger['rows']if r['status']=='CLOSED'for v in r['root_owners']]
 for r in refs:assert statements[r['root']]['owner_module']==r['owner_module']and H(statements[r['root']]['obligation_statement'].encode())==r['obligation_statement_sha256']
 oversized=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not oversized
 changed=subprocess.check_output(['git','diff','--name-only','908c9aa7384^'],text=True).splitlines();assert all(n.startswith('evidence/ledger25-20261111/NMQ_')for n in changed)
 x=dict(status='PASS',compressed_sha_pairs=archives,source_snapshots_checked=snapshots,scope_receipts=len(receipts),selected_Aeneas_pin_paths=len(aeneas),required_roots=len(statements),row_root_references=len(refs),distinct_canonical_row_roots=len({r['root']for r in refs}),mutations=mutants,files_over20MB=oversized,shipped_source_changes=[],keys_accounts_funds_authorities_touched=False,push=False)
 (E/'NMQ_VALIDATION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
if __name__=='__main__':main()
