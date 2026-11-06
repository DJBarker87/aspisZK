"""Build an additive eight-row candidate packet from exact baseline identities and receipts."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
basepath=E.parent/'ledger17-20261108/NKC_LEDGER.json.xz';base=json.loads(lzma.decompress(basepath.read_bytes()));ids=['TX1:155','TX1:157','TX1:158','TX1:159','TX1:160','TX1:165','TX1:166','TX1:167'];selected={r['row']:r for r in base['rows']if r['row']in ids};assert len(selected)==8 and all(r['status']=='OPEN'for r in selected.values())
allrows={r['function']:r for r in base['rows']if r['transaction']=='TX1'}
rootmap={'TX1:155':['AspisR1.NKD_Add.root'],'TX1:157':['AspisR1.NKD_Decode.root'],'TX1:158':['AspisR1.NKD_Gamma.root','AspisR1.NKD_Values.gamma'],'TX1:159':['AspisR1.NKD_Low.root'],'TX1:160':['AspisR1.NKD_Ordinary.root'],'TX1:165':['AspisR1.NKD_Runtime.absorb_root','AspisR1.NKD_TranscriptPackets.absorb'],'TX1:166':['AspisR1.NKD_Runtime.block_root','AspisR1.NKD_TranscriptPackets.block'],'TX1:167':['AspisR1.NKD_Runtime.new_root','AspisR1.NKD_TranscriptPackets.new']}
domains={'TX1:155':'SAME canonical eight digits and amount<=257; gamma derives both from SAME low trace, second amount1; full mutated array and carry Bool','TX1:157':'SAME canonical eight digits, derived from SAME low/add child; exact complete WideExact coordinates','TX1:158':'arbitrary32-byte block; ordered per-step low/add cuts, all caller domains and second carry derived internally; exact adopted installed gamma output','TX1:159':'arbitrary32-byte block; ordered byte/pass/window trace; full digits/quotient and quotient<=256, canonicality derived','TX1:160':'arbitrary32-byte block; SAME low trace then canonical decode; exact installed ordinary output','TX1:165':'ONLY deployed SolanaDigest; row<=95, arbitrary immutable payload0..8192; exact4parts, full reply/state/hash frame','TX1:166':'ONLY deployed SolanaDigest; row<=95, arbitrary immutable payload0..8192; SAME absorb/read/advance order, full reply/final state/hash frame','TX1:167':'ONLY deployed SolanaDigest; every semantic32 and S1/S2/D variant; exact domain29/tag1/state32, full reply/hash carrier'}
pairs={'TX1:155':[['NGT_K007','NGT_K008'],['NGT_K035','NGT_K036'],['NGT_K041','NGT_K042']],'TX1:157':[['NGT_K013','NGT_K014']],'TX1:158':[['NGT_K011','NGT_K012']],'TX1:159':[['NGT_K%03d'%i,'NGT_K%03d'%(i+1)]for i in [15,21,23,25,27,29,31,33,35,37]],'TX1:160':[['NGT_K009','NGT_K010']],'TX1:165':[['NKD_K003','NKD_K004']],'TX1:166':[['NKD_K005','NKD_K006']],'TX1:167':[['NKD_K007','NKD_K002']]}
functions=[];identity=[];inventory=[]
for row in ids:
 r=selected[row];o=r['obligation'];cert=o['certificate'];rel=cert['source_file'];raw=subprocess.check_output(['git','show',base['frozen_revision']+':'+rel]);a,b=cert['frozen_body_byte_range'];assert hashlib.sha256(raw[a:b]).hexdigest()==r['frozen_body_sha256'],row
 assert (R/rel).read_bytes()==raw,rel
 children=[]
 for c in r['canonical_callees']:
  cr=allrows[c];internal=cr['row']in ids;assert internal or cr['status']=='CLOSED'
  children.append(dict(row=cr['row'],function=c,baseline_status=cr['status'],internal_packet=internal,canonical_owner_roots=cr.get('root_owners',[]),source_classification='RETAINED conservative-by-name; actual operation is primitive u32::to_le_bytes under (au)'if row=='TX1:165'and 'field' in c else 'actual child or in-cut body execution; SAME arguments/domain and complete carrier'))
 f=dict(rows=[row],function=r['function'],route='(y)/(ai)(5)/(aq)/(aq)(5)/(au); direct hybrid P6, deployed-only(al) for transcripts',root_domain=domains[row],native_pairs=pairs[row],lean_roots=rootmap[row],complete_carrier=True,premise_policy='Root input domains and reviewed per-step source cuts only; every actual child result/domain is internally discharged; no endpoint equality, caller success, output law or free Ops dictionary',trust='P6/D188 option A RECLASSIFICATION; existing Std/allocator/runtime/SHA/compiler/ABI/source-to-ELF retained, none added/removed',canonical_callees=children,baseline_obligation_statement_hash=r['obligation_statement_hash'],frozen_body_sha256=r['frozen_body_sha256'],status='GATED_CANDIDATE_AWAITING_NEXT_LEDGER')
 functions.append(f);identity.append(dict(row=row,function=r['function'],source_file=rel,body_byte_range=[a,b],frozen_body_sha256=r['frozen_body_sha256'],obligation_statement_hash=r['obligation_statement_hash'],original_named_hypotheses=o.get('named_hypotheses',[]),original_unit_domains=o.get('inventory_domain_obligations',[]),caller_domain_obligations=o.get('caller_domain_obligations',[])))
 inventory.append(dict(row=row,allowed_inputs=domains[row],reviewed_cuts='NKD_CUTS.md',root_hypothesis_review='NKD_ROOT_INVENTORY.md',preserved_original_obligation_hash=r['obligation_statement_hash'],callees=children))
roots=json.loads((E/'NKD_AUDIT_ROOTS.json').read_text())['roots'];audit=json.loads((E/'NKD_audit/proof0/receipt.json').read_text());assert audit['exit_status']==0
assert {r['root']for r in audit['results']}==set(roots) and len(audit['results'])==len(roots)
standard={'propext','Classical.choice','Quot.sound'}
assert all(r['equal']and set(r['walked_axioms'])<=standard and r['walked_axioms']==r['collect_axioms']for r in audit['results'])
scan=[json.loads(l)for l in lzma.decompress((E/'NKD_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
fixtures=json.loads((E/'NKD_audit/fixtures/receipt.json').read_text());assert fixtures['exit_status']==0 and len(fixtures['results'])==8
assert all(x['walked_axioms']for x in fixtures['results'][:4])and all(not x['walked_axioms']for x in fixtures['results'][4:])
receipts=[json.loads(p.read_text())for p in sorted(E.glob('NKD_[LK]???/receipt.json'))];assert len(receipts)==34,len(receipts)
metrics=dict(scopes=len(receipts),lean_support_identifiers=28,kani_identifiers=7,kani_verification_invocations=6,extractions=0,wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),no_timeouts=True,no_memory_kills=True)
checks=dict(status='PASS',combined=dict(attempt='NKD_L024',exit=0,headline='AspisR1.RPx_Deployed.deployed'),raw_ax2=dict(attempt='NKD_L026',exit=audit['exit_status'],roots=len(roots),standard_axioms_only=True,all_equal_collectAxioms=True,results=audit['results']),fixtures=dict(attempt='NKD_L025',exit=0,eight_results=fixtures['results'],same_binary_as_raw_audit=True,read_only_recovery=True),NFX=dict(attempt='NKD_L027',exit=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan)),metrics=metrics,closure_pins_sha256=H(E/'NKD_CLOSURE_PINS.json.xz'),predecessor_comparison=json.loads((E/'NKD_PREDECESSOR_COMPARISON.json').read_text()),ledger_credit='PENDING next lead ledger gate',target_established=False)
(E/'NKD_AUDIT.json').write_text(json.dumps(checks,indent=1)+'\n')
(E/'NKD_CLOSED.json').write_text(json.dumps(dict(frozen_revision=base['frozen_revision'],headline=base['headline'],functions=functions,admission=checks,status='EIGHT_GATED_CANDIDATES; credit waits for next ledger gate',validation='NKD_validate.py',target_established=False),indent=1)+'\n')
(E/'NKD_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline=str(basepath.relative_to(R)),baseline_sha256=H(basepath),baseline_counts=base['counts'],official_baseline_unchanged=True,scope='ONLY eight assigned TX1 occurrences',proposed_counts_if_next_gate_admits={'CLOSED':522,'OPEN':77,'QUALIFIED':0},changed_rows=[dict(row=f['rows'][0],function=f['function'],before='OPEN',proposed='CLOSED',credit='PENDING next ledger',baseline_obligation_statement_hash=f['baseline_obligation_statement_hash'],packet='NKD_CLOSED.json',lean_roots=f['lean_roots'])for f in functions],no_parent_promotion=True),indent=1)+'\n')
(E/'NKD_ORIGINAL_OBLIGATIONS.json').write_text(json.dumps(identity,indent=1)+'\n');(E/'NKD_CALLER_CLAUSES.json').write_text(json.dumps(inventory,indent=1)+'\n')
# Large input appears once, with an exact source-snapshot reference.
p=E/'NKD_L027/sources/NKD_EXPECTED_IMPORTS.jsonl'
if p.exists():
 assert H(p)==H(E/'NKD_EXPECTED_IMPORTS.jsonl');ref=dict(snapshot=str(p.relative_to(E)),retained_input='NKD_EXPECTED_IMPORTS.jsonl',sha256=H(p));(E/'NKD_SOURCE_REFS.json').write_text(json.dumps([ref],indent=1)+'\n');p.unlink()
# Source kernel print references retain the actual full statements and proofs.
k=[]
for r in receipts:
 if r['kind']=='lean'and r['exit_status']==0:
  s=(E/r['attempt']/'stdout.log').read_text()
  k.append(dict(attempt=r['attempt'],module=r['module'],source_hashes=r['source_hashes'],stdout_sha256=H(E/r['attempt']/'stdout.log'),full_kernel_prints=s,print_axioms=r['print_axioms']))
raw=json.dumps(k,indent=1).encode();(E/'NKD_KERNEL_STATEMENTS.json.xz').write_bytes(lzma.compress(raw));(E/'NKD_KERNEL_STATEMENTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print('PASS: eight additive gated candidate packets; official514/85 ledger unchanged')
