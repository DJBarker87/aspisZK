#!/usr/bin/env python3
"""Bottom-up SCC order on canonical frozen edges; no status promotion."""
import collections,json,lzma,pathlib,subprocess
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
L=json.loads(lzma.open(R/'evidence/ledger6-20261104/NFK_LEDGER.json.xz').read());S=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())['slices'];D=set(json.loads((E/'NFQ_SLICE_D.json').read_text())['slices']['D']['functions'])
ix=collections.defaultdict(list)
for r in L['rows']:ix[r['function']].append(r)
graph={f:sorted({c for r in ix[f] for c in r['canonical_callees'] if c in D}) for f in D}
# Tarjan gives sink components first, retaining conservative recursive cycles.
index={};low={};stack=[];on=set();components=[]
def visit(v):
 index[v]=low[v]=len(index);stack.append(v);on.add(v)
 for w in graph[v]:
  if w not in index:visit(w);low[v]=min(low[v],low[w])
  elif w in on:low[v]=min(low[v],index[w])
 if low[v]==index[v]:
  comp=[]
  while True:
   w=stack.pop();on.remove(w);comp.append(w)
   if w==v:break
  components.append(sorted(comp))
for f in sorted(D):
 if f not in index:visit(f)
ci={f:i for i,c in enumerate(components) for f in c};assert all(ci[c]<=ci[f] for f in D for c in graph[f])
first=['crates/aspis-r1-cost-probe/src/compact.rs::compact_row','crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape','crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds','crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len','crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size']
records=[]
for comp in components:
 for f in comp:
  rr=ix[f];callees=sorted({c for r in rr for c in r['canonical_callees']});file=f.split('::')[0]
  # Read-only frozen body, using exact stored inventory byte range.
  src=subprocess.check_output(['git','show',L['frozen_revision']+':'+file],cwd=R)
  start,end=rr[0]['frozen_body_byte_range'];body=src[start:end].decode()
  loops=('while ' in body or 'for ' in body or '.iter(' in body or '.fold(' in body)
  shapes=['(y) frozen caller Result/state/ordered-effects oracle certificate; matched corrupt argument/reply control; child domain and modifies frame; Lean substitution equality; ax2 raw audit']
  if loops:shapes+=['One arbitrary-prestate native iteration plus Lean invariant/induction. Use (ad) only after proving data-independent control, including abort prefixes. No whole-buffer Kani.']
  if 'obs' in body or 'observer' in f or 'mark'==f.rsplit('::',1)[-1]:shapes+=['(ae)/(z)(1): deployed constant None, no pointer assertions, rename-stability pair, erased-phase Lean trace; rule14 otherwise quarantines.']
  if 'digest' in body or 'hashv' in body:shapes+=['Runtime digest value retained trust; certify exact byte slices, call position and unchanged reply; never unwind SHA.']
  if any(x in body for x in ['copy_from_slice','clone_from_slice','extend_from_slice','to_vec','clone()']):shapes+=['Exact KMX patch and same-configuration failing copy control; arbitrary window/frame lift.']
  if 'Box' in body:shapes+=['(aa) same allocated Box value/identity and error cleanup; corrupt-value and wrong-allocation controls.']
  packets=[]
  for c in callees:
   cr=ix[c];membership=[s for s in S if c in S[s]['functions']]
   packets.append(dict(function=c,scope='opaque '+','.join(membership) if membership else ('D SCC '+str(ci[c]) if c in D else 'slice boundary'),rows=[r['row'] for r in cr],baseline_status={r['row']:r['composed_status'] for r in cr},existing_packets=sorted({p for r in cr for p in r['active_support_receipts']})))
  records.append(dict(function=f,component=ci[f],recursive_component=len(comp)>1 or f in graph[f],rows=[r['row'] for r in rr],callees=packets,certificate_shape=shapes,native_domain=[x for r in rr for x in r['inventory_domain_obligations']],existing_support=sorted({p for r in rr for p in r['active_support_receipts']}),first_five=f in first))
(E/'NFQ_ORDER.json').write_text(json.dumps(dict(first_five=first,components=components,functions=records),indent=2)+'\n')
t=['# Bottom-up D order','', '**Plan, not closure.** NFQ_ORDER.json enumerates every OPEN function, exact callee rows and existing receipt packets, inventory domains, SCC and certificate shape. Components are ordered callee before caller. Conservative receiver ambiguity can create artificial cycles; a cycle must be resolved against frozen receiver types before claiming a real recursive certificate.', '', '## First five candidates with existing interface shapes','']
for i,f in enumerate(first,1):t.append(f'{i}. `{f}`: '+('all u8, pure Bool; NCO extracted reference/cohort law and scalar body contract exist.' if i==1 else 'all u8, Option<(u8, usize)>; NCO extracted reference/cohort law and controls exist; no substitution of an unadmitted returned-reference carrier.' if i==2 else 'all three variants; scalar result, NBG_Transport emitted/cohort equations. Actual-body contract may execute scalar callees directly; no stub_verified interface needed.'))
t+=['', 'These are candidates for certification now, not an assertion that their inherited packets pass ax2 or current rule16 review. Prior NCO/transport native inputs must be revalidated before credit. No new extraction is needed if those exact extracted references and pins are reused. Order folds before final_len before checkpoint_size.', '', '## TX1 spine priority after scalar leaves','', 'prepare -> Prepared::new / powers / verify_observed requires full Result, owned prepared/scratch carriers, original proof/public bytes and digest order. Compact expansion/checking and semantic transcript depend on compact_row/row_shape; checkpoint writer depends on checkpoint_size and the existing checkpoint opaque packet. query_loop remains an opaque OPEN Q boundary pending NFP. Do not hold independent D leaves behind it.', '', 'finish_query_dot has Q-boundary EbyKDot::push (OPEN in NFK, later Q support must be validated); it may proceed once that callee packet is imported with domain proof. Pool settlement consumer is outside the inventory and owned by NFO; no new outside-slice bridge is attempted.', '', '## Ordered components','']
for i,c in enumerate(components):t.append(f'{i}: '+ '; '.join('`'+f+'`' for f in c))
(E/'NFQ_ORDER.md').write_text('\n'.join(t)+'\n')
print(json.dumps(dict(components=len(components),functions=len(records),first_five=first)))
