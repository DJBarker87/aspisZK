from pathlib import Path
import json,hashlib,lzma,base64,re,collections
E=Path(__file__).resolve().parent
aliases={r['path']:r['retained']for r in json.loads((E/'NJB_DEDUP.json').read_text())}if(E/'NJB_DEDUP.json').exists()else{}
def data(n):
 p=E/n
 if p.exists():return p.read_bytes()
 if n in aliases:return data(aliases[n])
 raise FileNotFoundError(n)
def J(n):return json.loads(data(n))
entries=[json.loads(l)for l in data('NJB_ATTEMPTS.jsonl').decode().splitlines()];counts=collections.Counter(x['attempt'][4]for x in entries);assert counts=={'K':120,'L':100,'E':1},counts
by={x['attempt']:x for x in entries};assert len(by)==len(entries)
for x in entries:
 lim=x['limits'];assert lim['memory.high']=='6442450944'and lim['memory.max']=='8589934592'and lim['memory.swap.max']=='0'and lim['pids.max']=='64'
 admission=J(x['attempt']+'-admission.json');assert admission['exit']==0 and admission['reservation']['allowed'] is True
pairs=[(5,2),(6,7),(14,15)]+[(i,i+1)for i in range(20,34,2)]+[(40,41),(46,47),(44,45),(36,37),(38,39)]+[(i,i+1)for i in range(48,54,2)]+[(62,63),(64,65)]+[(i,i+1)for i in range(66,72,2)]+[(96,97)]+[(i,i+1)for i in range(84,96,2)]+[(i,i+1)for i in range(98,134,2)]+[(141,142),(143,144),(136,137)]
assert len(pairs)==51
native=[]
for p,n in pairs:
 pa=f'NJB_K{p:03}';na=f'NJB_K{n:03}';pos=by[pa];neg=by[na]
 plog=data(pa+'/stdout.log').decode();nlog=data(na+'/stdout.log').decode();assert pos['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL'in plog,pa
 assert neg['exit_status']==1 and 'VERIFICATION:- FAILED'in nlog and 'timed out'not in nlog.lower()and'error[E'not in nlog,na
 for a,x in [(pa,pos),(na,neg)]:
  g=J(a+'-graph-check.json');l=J(a+'-lock-check.json');s=J(a+'-source-check.json')
  assert g['graph_matches_frozen']is True and not g['new_package_tuples']and not g['edge_errors'],a
  assert l['unchanged']is True and l['before']==l['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  assert not s['errors'],a
  assert x['env']['CARGO_NET_OFFLINE']=='true';assert '--locked'not in x['native_command'];assert x['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'
  log=data(a+'/stdout.log').decode();assert not('unwinding assertion' in log.lower()and 'FAILURE' in log),a
 native.append(dict(positive=pa,negative=na,harness=pos['native_command'][pos['native_command'].index('--harness')+1],root_package=pos['root_package'],source_revision=pos['source_revision'],graph=pa+'-graph-check.json',lock=pa+'-lock-check.json'))
assert 'NJB_K134' in by and 'timed out' in data('NJB_K134/stdout.log').decode().lower()
fixtures=J('NJB_audit/fixtures/receipt.json');assert fixtures['exit_status']==0 and fixtures['fixture_pass']and len(fixtures['results'])==8
proofs=[J('NJB_audit/proof'+str(i)+'/receipt.json')for i in range(2)];actual=[]
for p in proofs:
 assert p['exit_status']==0 and p['standard_only'];actual+=p['results']
roots=J('NJB_AUDIT_ROOTS.json')['roots'];assert {r['root']for r in actual}==set(roots)and len(actual)==len(roots)
for r in actual:assert r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
scan=J('NJB_audit/scan/receipt.json');assert scan['exit_status']==0 and not(scan['dangling']or scan['duplicate_owners']or scan['import_mismatch'])
raw=lzma.decompress(base64.b64decode(data('NJB_audit/scan/scan.jsonl.xz.b64.txt')));assert hashlib.sha256(raw).hexdigest()==data('NJB_audit/scan/scan.jsonl.sha256').decode()
shipped=J('NJB_SHIPPED_CHECK.json');assert all(r['frozen_tree']==r['head_tree']and not r['dirty']for r in shipped['trees'])
export=J('NJB_EXPORT.json');assert export['delete_cache'] is False
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';obligations=json.loads(lzma.decompress(data('NJB_OBLIGATIONS.json.xz')));row=next(r for r in obligations if r['row']=='TX1:268')
function=dict(rows=['TX1:268'],function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],route='direct native/cohort constructor identity P6 hybrid',root_domain='every typed terminal statement, both variants and every common/public field value',native_pairs=[['NJB_K005','NJB_K002']],lean_roots=['AspisR1.NJB_SemanticPublic.result'],owner_module='NJB_SemanticPublic',complete_carrier=True,premise_policy='typed input statement only; no child/success/endpoint/Run hypothesis',trust='P6/D188 option A RECLASSIFICATION; existing ABI/std/compiler/source-to-ELF and enclosing codec obligations retained; none added/removed')
(E/'NJB_CLOSED.json').write_text(json.dumps(dict(frozen_revision=frozen,headline='AspisR1.RPx_Deployed.deployed',functions=[function],local_gate='PASS',credit_waits_next_ledger_gate=True,other_new_packets='SUPPORT ONLY'),indent=1))
audit=dict(status='PASS',target_not_established=True,baseline='evidence/ledger13-20261107/NIU_LEDGER.json.xz',baseline_counts=dict(CLOSED=432,QUALIFIED=0,OPEN=167,total=599),target_occurrences=32,proposed_rows=['TX1:268'],authoritative_ledger_edited=False,credit_waits_next_ledger_gate=True,budget=dict(used=dict(kani=counts['K'],lean_support=counts['L'],extraction=counts['E']),limit=dict(kani=120,lean_support=100,extraction=1)),native_pairs=native,additional_cache_identity_control=None,excluded_kani=dict(compiler=[1,3,4,12,80],timeouts=[8,10,54,60,72,82,134],unwinding=[34,42],reduced_prepared_token=[16,17,18,19]),compiled_proof_modules=len(J('NJB_GATE_SOURCES.json')['passed']),raw_axiom_roots=len(roots),raw_axiom_standard_only=True,walker_fixtures=8,scan=dict(modules=scan['modules'],dangling=scan['dangling'],duplicate_owners=scan['duplicate_owners'],import_mismatch=scan['import_mismatch']),standard_axioms=['propext','Classical.choice','Quot.sound'],new_trust_rows=[],removed_trust_rows=[],transport='P6/D188 option A reclassification',source_tree_check='NJB_SHIPPED_CHECK.json',elf_rebuilt=False,retained_export=dict(path=export['cache'],bytes=export['bytes']),option_fn_quarantined=[],writable_static_suspended=[],kani_contracts_used=False,source_revision_per_attempt=True,metrics_per_attempt='NJB_ATTEMPTS.jsonl and full_receipt',exact_native_target='native_command --harness is authoritative; early module display labels can be stale',root_hypotheses={'TX1:268':['typed input statement']})
(E/'NJB_AUDIT.json').write_text(json.dumps(audit,indent=1))
(E/'NJB_LEDGER_DELTA.json').write_text(json.dumps(dict(operation='proposed additive delta; authoritative baseline not edited',base=audit['baseline'],baseline_sha256=hashlib.sha256((E.parent/'ledger13-20261107/NIU_LEDGER.json.xz').read_bytes()).hexdigest(),added_closed_rows=['TX1:268'],credit_waits_next_ledger_gate=True,validation=dict(status='PASS',roots=len(roots),modules=audit['compiled_proof_modules'],scanned_modules=scan['modules'],kani=120,lean_support=100,extraction=1),unchanged_open_rows=[r['row']for r in obligations if r['row']!='TX1:268'],headline='AspisR1.RPx_Deployed.deployed',headline_hypotheses_removed=[],new_trust_rows=[]),indent=1))
print(json.dumps(dict(status='PASS',candidate_rows=1,kani=120,lean_support=100,extraction=1,raw_roots=len(roots),scan_modules=scan['modules'])))
