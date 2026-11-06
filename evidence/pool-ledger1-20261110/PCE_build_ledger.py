"""Derive each occurrence from NKZ and immutable gate packets; no invented roots."""
from pathlib import Path
import json,lzma,hashlib,collections
E=Path(__file__).resolve().parent;R=E.parent
read=lambda p:json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def inputs():
 names=['pool-inventory2-20261109/NKZ_INVENTORY.json','pool-inventory2-20261109/NKZ_TRACTABILITY.json','pool-inventory2-20261109/NKZ_OBLIGATIONS.json','ledger23-20261110/NLO_LEDGER.json.xz','pc-helpers1-20261110/PCB_CLOSED.json','pc-helpers1-20261110/PCB_CANDIDATES.json','pc-helpers1-20261110/PCB_CALLER_CLAUSES.json']
 return {n:sha(R/n) for n in names}
def build():
 inv=read(R/'pool-inventory2-20261109/NKZ_INVENTORY.json');tract={r['row']:r for r in read(R/'pool-inventory2-20261109/NKZ_TRACTABILITY.json')['rows']};a=read(E/'PCE_AUDIT.json');assert a['status']=='PASS'
 basis=read(R/'ledger23-20261110/NLO_LEDGER.json.xz');br={r['row']:r for r in basis['rows']};packets={r['id']:r for n in ['PCB_CLOSED.json','PCB_CANDIDATES.json'] for r in read(R/'pc-helpers1-20261110'/n)}
 clauses=read(R/'pc-helpers1-20261110/PCB_CALLER_CLAUSES.json');statements=read(E/'PCE_STATEMENTS.json');raw={r['root']:r for r in a['roots']};byfun={r['function']:r for r in inv['rows']};incoming=collections.defaultdict(list)
 for caller in inv['rows']:
  for index,edge in enumerate(caller['edges']):
   for fn in edge['targets']:
    if fn in byfun:incoming[byfun[fn]['id']].append(dict(caller=caller['id'],edge_index=index,kind=edge['kind'],line=edge['line'],source='NKZ_INVENTORY.json:rows/edges; conservative alternatives retained'))
 rows=[]
 for r in inv['rows']:
  rid=r['id'];new=r['genuinely_new'];packet=packets.get(rid);rec=dict(id=rid,function=r['function'],class_=tract[rid]['class_'] if new else 'SHARED',ownership='STREAM-C' if new else 'STREAM-A-SHARED',status='OPEN',credited_pool_row=False,root=None,exact_statement=None,named_hypotheses=None,caller_clauses=[],trust_items_used=[],evidence_pointer='evidence/pool-inventory2-20261109/NKZ_INVENTORY.json#'+rid,gate_attempt=None,frozen_body_sha256=r['frozen_body_sha256'],source_lines=r['source_lines'],incoming_occurrences=incoming[rid],callees=[byfun[f]['id'] for f in r['callees'] if f in byfun],privacy_flag='NO-PRIVACY-CREDIT',error_emission_abstraction='UNASSESSED; no source bridge or privacy credit',same_argument_requirement='Every use must discharge the complete callee domain on SAME arguments, carrier, state and ordered effects; body identity alone gives no caller-domain closure.')
  if not new:
   matches=[]
   for o in r['basis_overlap']:
    b=br[o['row']];assert b['function']==r['function'] and b['frozen_body_sha256']==r['frozen_body_sha256']
    matches.append(dict(row=b['row'],status=b['status'],root_owners=b['root_owners'],exact_statements=b['obligation']['kernel_roots'],named_hypotheses=b['obligation']['named_hypotheses'],caller_clauses=b['obligation']['caller_domain_obligations'],inventory_clauses=b['obligation']['inventory_domain_obligations'],certificate=b['obligation']['certificate'],evidence=b['evidence_dir']))
   rec.update(status='CLOSED' if all(m['status']=='CLOSED' for m in matches) else 'OPEN',matched_stream_a_rows=matches,root=[p['root'] for m in matches for p in m['root_owners']],exact_statement=[m['exact_statements'] for m in matches],named_hypotheses=[m['named_hypotheses'] for m in matches],caller_clauses=[m['caller_clauses'] for m in matches],gate_attempt='ledger23/NLS_L001..040; consumed as previously gated packets in PCE_L001/PCE_L008',evidence_pointer='evidence/ledger23-20261110/NLO_LEDGER.json.xz',privacy_flag='SOUNDNESS-ONLY',error_emission_abstraction='Pool occurrence effect/ABI association is not established here; shared soundness packet never cited as error-path privacy evidence')
   matched={m['row'] for m in matches};rec['trust_items_used']=[t for t in basis['trust_rows'] if matched.intersection(t.get('direct_closed_rows',[])+t.get('retained_value_realization_uses',[]))]
   rec['trust_context_retained']='Complete ledger23 trust inventory and each matched certificate retained; runtime rows apply only where stated, no new Pool caller instance.'
  elif packet:
   root=packet['root'];assert root in raw and set(raw[root]['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
   assert packet.get('frozen_body_sha256',packet.get('body_hash',r['frozen_body_sha256']))==r['frozen_body_sha256']
   rec.update(status='CLOSED',credited_pool_row=True,root=root,exact_statement=packet['statement'],named_hypotheses=packet['named_hypotheses'],caller_clauses=dict(domain=packet['caller_clause'],named_hypotheses=packet['named_hypotheses'],uses=[c for c in clauses if c.get('callee')==rid]),trust_items_used=[dict(id='P6/D188-option-A',status='RECLASSIFICATION retained, never removal',scope=packet['trust']),dict(id='Rust-Std-Compiler-ABI-SourceToELF',status='RETAINED',scope='Exact frozen body and inherited deployed feature resolution; no new ELF rebuild')],evidence_pointer='evidence/pc-helpers1-20261110/'+('PCB_CANDIDATES.json' if packet.get('status')=='OPEN_GATE_BLOCKED' else 'PCB_CLOSED.json'),gate_attempt=a['root_attempts'][root],raw_axioms=raw[root]['walked_axioms'],checked_statement=statements[root],inherited_packet=packet,privacy_flag='NO-PRIVACY-CLAIM',error_emission_abstraction=False)
   if rid=='POOL:344':rec['trust_items_used'].append(dict(id='RuntimeReturnDataClear',status='ACCEPTED retained',scope='Exact empty request and unit reply, no new value realization'))
  else:
   rec.update(obligation='Complete frozen deployed function source-to-model bridge, exact Result/abort/effect paths and all caller/callee domains remain unproved.',open_reason=tract[rid]['reason'],required_route=tract[rid]['route'])
   if rid in ['POOL:328','POOL:330']:
    rec['required_runtime_items']=[dict(id='RuntimeCpiAccountView',status='ADDED-LEAD-20261110',scope='Returning invoke: excluded keys unchanged data/lamports/owner; passed matching keys reflect callee final values. No SDK guard/handle/key/flag frame or CPI success.')]
    rec['caller_clauses']=['SAME reached guards and account cells; require_unique_accounts plus admitted equal-key/cell facts; exact instruction metas and passed infos; SDK guard/counter preservation; callee effects and all returning continuations.']
  rows.append(rec)
 counts=collections.Counter(r['class_'] for r in rows if r['credited_pool_row']);n=sum(counts.values());shared=sum(r['ownership']=='STREAM-A-SHARED' and r['status']=='CLOSED' for r in rows)
 return dict(schema='PCE-POOL-LEDGER-1',headline='AspisR1.RPx_Deployed.deployed',security_target_established=False,gate='PASS',frozen_pool_revision=inv['frozen_revision'],frozen_crates_revision=inv['crates_revision'],pool_elf_sha256=inv['pool_elf_sha256'],pins_inherited_not_rebuilt=True,source_pins=inputs(),rows=rows,counts=dict(new_total=278,new_closed=n,new_open=278-n,new_candidate=0,closed_by_class={k:counts[k] for k in 'ABCD'},shared_total=119,shared_consumed_closed=shared,guard_owners_on_closed=0,guard_owners_on_total=3),trust_inventory_context=basis['trust_rows'],new_runtime_trust_item=dict(id='RuntimeCpiAccountView',status='ADDED-LEAD-20261110',used_by_closed_PCE_roots=False,required_by_open_rows=['POOL:328','POOL:330']),scope='Pool body closure only; shared rows retain Stream A ownership and do not add to278; no parent composition, privacy or release-target closure')
def write_ledger(x):
 raw=(json.dumps(x,indent=1)+'\n').encode();p=E/'PCE_LEDGER.json'
 if len(raw)>20_000_000:
  (E/'PCE_LEDGER.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'PCE_LEDGER.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(raw)
if __name__=='__main__':
 x=build();write_ledger(x);c=x['counts'];(E/'PCE_COUNT.md').write_text(f"Pool rows CLOSED: {c['new_closed']} of 278 new (A {c['closed_by_class']['A']} / B {c['closed_by_class']['B']} / C {c['closed_by_class']['C']} / D {c['closed_by_class']['D']}); shared consumed: {c['shared_consumed_closed']} of 119 bodies CLOSED in ledger23; guard owners CLOSED: 0 of 3 ON; target not yet established\n")
 print('Built authoritative397-occurrence Pool ledger: '+str(c['new_closed'])+' new CLOSED, '+str(c['shared_consumed_closed'])+' shared bodies consumed; target not yet established.')
