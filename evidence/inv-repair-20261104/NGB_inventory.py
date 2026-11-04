"""NGB additive successor to NFZ_inventory.apply.
Adds explicit OPEN occurrences before reviewed edges; preserves all baseline rows,
statuses and adjacency. Every addition is pinned by MIR and frozen-source AST.
"""
import json,lzma,pathlib,hashlib,collections,copy,re,subprocess
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1];Z=R/'evidence/inv-defects-20261104'
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
def pin(p):return dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
base=json.loads(lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read())
D=json.loads(lzma.open(E/'NGB_SOURCE_AST.json.xz').read());decl={d['function']:d for d in D}
M=json.loads((E/'NGB_MIR_EDGES.json').read_text());candidates=json.loads((Z/'NFZ_CANDIDATES.json').read_text())['candidates']
root='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction'
G=collections.defaultdict(set)
for r in base['rows']:G[r['function']].update(r['canonical_callees'])
original=copy.deepcopy(G)
def closure(g,roots):
 seen={f:[f] for f in roots};q=collections.deque(roots)
 while q:
  f=q.popleft()
  for c in sorted(g.get(f,[])):
   if c not in seen:seen[c]=seen[f]+[c];q.append(c)
 return seen
# Admit only newly missing edges from candidate callers and the mandatory stage2 callback.
selected={c['caller'] for c in candidates}|{'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned'}
# Census canonical owner for stage2 is confirmed from source declaration.
selected|={d['function'] for d in D if d['name']=='stage2_owned'}
edges=[]
def add(f,t,records,kind='trait-dispatch'):
 if t in G[f]:return False
 assert records and all(x['source_check']=='AGREES' for x in records)
 edges.append(dict(**{'from':f,'to':t},kind=kind,evidence=dict(path='evidence/inv-repair-20261104/NGB_MIR_EDGES.json',sha256=sha((E/'NGB_MIR_EDGES.json').read_bytes()),method='rustc-MIR',compiler_gate_passed=True,records=[x['id'] for x in records])))
 G[f].add(t);return True
changed=True
while changed:
 changed=False;reached=closure(G,[root]);groups=collections.defaultdict(list)
 for m in M['edges']:
  if m['caller'] in selected and m['caller'] in reached and not m['generic_uninstantiated']:groups[(m['caller'],m['callee'])].append(m)
 for (f,t),rr in groups.items():changed|=add(f,t,rr,'callback' if t.endswith(('::error','::circle_fallback_point')) else 'trait-dispatch')
# New functions' complete native project callees. Parse the retained MIR bodies,
# not the source call graph; source AST is a required second check.
blocks={}
for p in [Z/'NFZ_aspis_core.mir.xz',Z/'NFZ_B005_aspis_r1_cost_probe-2af8d844c3814c6b.mir.xz',Z/'LEAD_B006/aspis_r1_cost_probe_program.mir.xz']:
 h='';lines=[];start=0
 for i,l in enumerate(lzma.open(p,'rt'),1):
  if l.startswith('fn '):
   if h:blocks.setdefault(h,(p,start,lines))
   h=l.strip();start=i;lines=[]
  lines.append((i,l.strip()))
 if h:blocks.setdefault(h,(p,start,lines))
def block_for(f):
 d=decl[f];tail=f.split('::')[-1];found=[]
 for h,b in blocks.items():
  if not re.search(r'::'+re.escape(tail)+r'\(|^fn '+re.escape(tail)+r'\(',h):continue
  im=re.search(r'<impl at ([^:]+):(\d+):',h)
  if im:
   if im[1]==d['file'] and int(im[2])==d['impl_start']:found.append((h,b))
  elif h.startswith('fn '+tail+'(') and len([x for x in D if x['name']==tail])==1:found.append((h,b))
 assert len(found)==1,(f,len(found))
 return found[0]
def resolve_call(expr,f):
 expr=expr.strip();p=f.split('::')[0]
 tr=re.fullmatch(r'<(M31|CM31|QM31|WideExact) as (?:aspis_core::r0::)?CodeField>::(\w+)',expr)
 if tr:return 'crates/aspis-core/src/r0/scalar.rs::'+tr[1]+'::'+tr[2]
 m=re.fullmatch(r'(M31|CM31|QM31|WideExact)::(\w+)',expr)
 if m:return 'crates/aspis-core/src/'+('field/wide_exact.rs' if m[1]=='WideExact' else 'field.rs')+'::'+m[1]+'::'+m[2]
 xs=[d['function'] for d in D if d['name']==expr]
 if len(xs)==1:return xs[0]
 local=[x for x in xs if x.split('::')[0]==p]
 return local[0] if len(local)==1 else None
trans=[];new_nodes=set(closure(G,[root]))-set(original)
done=set()
while new_nodes-done:
 f=sorted(new_nodes-done)[0];done.add(f);assert f in decl,f
 h,(p,start,ls)=block_for(f);d=decl[f]
 for i,l in ls:
  m=re.search(r' = (.+?)\((?:copy|move|const|_|\))',l)
  if not m or ' -> [' not in l:continue
  expr=m[1];t=resolve_call(expr,f)
  if not t:continue
  meth=t.split('::')[-1]
  sites=[x for x in d['calls'] if re.search(r'(?:\.|::|^)'+re.escape(meth)+r'$',x['expression'])]
  assert sites,(f,t,expr)
  rec=dict(id=f'NGB_T{len(trans)+1:04}',caller=f,callee=t,caller_header=h,mir_path=str(p.relative_to(R)),mir_line=i,mir_text=l,source_sites=sites,source_check='AGREES',features=['pool-adapter','private-leaf-salts'],prover=False)
  trans.append(rec)
  if t not in G[f]:
   edges.append(dict(**{'from':f,'to':t},kind='transitive-native-call',evidence=dict(path='evidence/inv-repair-20261104/NGB_TRANSITIVE_MIR_EDGES.json',records=[rec['id']],method='rustc-MIR',compiler_gate_passed=True)))
   G[f].add(t)
  if t not in original:new_nodes.add(t)
put('NGB_TRANSITIVE_MIR_EDGES.json',dict(inputs=M['inputs'],edges=trans))
for e in edges:
 if e['evidence']['path'].endswith('NGB_TRANSITIVE_MIR_EDGES.json'):e['evidence']['sha256']=sha((E/'NGB_TRANSITIVE_MIR_EDGES.json').read_bytes())
# Explicit row definitions: propagate only newly admitted dependencies on each TX.
rows=copy.deepcopy(base['rows']);new_rows=[]
for tx in ['TX1','TX2']:
 ix={r['function']:r for r in rows if r['transaction']==tx};seed=[e for e in edges if e['from'] in ix];pending=collections.deque(e['to'] for e in seed)
 while pending:
  f=pending.popleft()
  if f in ix:continue
  d=decl[f];r=dict(row=f'{tx}:NGB{len(new_rows)+1:03}',transaction=tx,function=f,source_file=d['file'],source_line=d['start'],source_file_sha256=sha(subprocess.check_output(['git','show',base['frozen_revision']+':'+d['file']],cwd=R)),frozen_body_byte_range=d['body_range'],frozen_body_sha256=d['body_sha256'],frozen_body_verified=True,composed_status='OPEN',bridge_status='OPEN',canonical_callees=sorted(G[f]),selected_claims=[],active_support_receipts=[],NGB_new_occurrence=True,no_credit_reason='New inventory occurrence; no bridge or domain closure claimed')
  ix[f]=r;rows.append(r);new_rows.append(r);pending.extend(sorted(G[f]))
 # Attach canonical union edges only to occurrences present (NFZ semantics).
 for r in rows:
  if r['transaction']==tx:r['canonical_callees']=sorted(G[r['function']])
# Every old status preserved, edges additive; no caller statuses changed for new obligations.
for a,b in zip(base['rows'],rows):
 assert a['row']==b['row'] and a['composed_status']==b['composed_status']
 assert set(a['canonical_callees'])<=set(b['canonical_callees'])
put('NGB_EDGES.json',edges)
overlay=dict(schema_version=2,name='NGB reviewed additive inventory repair',frozen_revision=base['frozen_revision'],review_status='REVIEWED_PARTIAL_C0032_EVIDENCE_GAP',baseline=pin(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz'),edge_list=pin(E/'NGB_EDGES.json'),producer=pin(E/'NGB_inventory.py'),predecessor_producer=pin(Z/'NFZ_inventory.py'),new_rows=new_rows,excluded_rows=[],no_status_promotion=True,unresolved_candidates=['NFZ_C0032'])
put('NGB_OVERLAY.json',overlay)
# Replay overlay independently of discovery order.
def apply(b,o):
 assert sha((R/o['edge_list']['path']).read_bytes())==o['edge_list']['sha256']
 out=copy.deepcopy(b);out['rows']+=copy.deepcopy(o['new_rows']);ix=collections.defaultdict(list)
 for r in out['rows']:ix[r['function']].append(r)
 for e in json.loads((R/o['edge_list']['path']).read_text()):
  ev=e['evidence'];assert sha((R/ev['path']).read_bytes())==ev['sha256'];assert ev['compiler_gate_passed']
  assert e['from'] in ix and e['to'] in ix
  for r in ix[e['from']]:r['canonical_callees']=sorted(set(r['canonical_callees'])|{e['to']})
 return out
out=apply(base,overlay);assert out['rows']==rows
out['NGB_overlay']='evidence/inv-repair-20261104/NGB_OVERLAY.json'
raw=json.dumps(out,indent=1).encode();(E/'NGB_ADMITTED_LEDGER.json.xz').write_bytes(lzma.compress(raw));(E/'NGB_ADMITTED_LEDGER.json.sha256').write_text(sha(raw)+'\n')
resolved=[]
for c in candidates:
 f=c['caller'];t=c.get('to');n=int(c['id'][-4:])
 if 26<=n<=31:t='crates/aspis-core/src/field.rs::QM31::'+('mul' if n in [26,30] else 'sub')
 matches=[x for x in M['edges'] if x['caller']==f and x['callee']==t]
 if n==32:disp='UNRESOLVED-EVIDENCE';reason='Reached in baseline canonical graph, but body absent from all three supplied MIR files; NFZ_aspis_statement.mir is zero bytes. Source-only callback cannot be admitted or called NOT-REACHED.'
 elif n==34:disp='NOT-REACHED';reason='pool-adapter cfg excludes the legacy entry body (source line 79); program entry MIR has no map_err(error), only first_decoded and stage2_owned do.'
 elif any(e['from']==f and e['to']==t for e in edges):
  disp='ADMITTED';reason='MIR typed callee and independent frozen AST agree; newly reached dependencies get explicit OPEN occurrences.'
 elif t in original.get(f,set()):disp='DUPLICATE';reason='Typed MIR resolves the method to an existing canonical edge; no edge addition.'
 else:raise AssertionError((c['id'],f,t))
 duplicate=None
 if n==39:disp='DUPLICATE';reason='Same WideExact trait-impl call site as NFZ_C0001; admitted once.';duplicate='NFZ_C0001'
 resolved.append(dict(candidate=c['id'],caller=f,callee=t,source_line=c['line'],disposition=disp,reason=reason,duplicate_of=duplicate,mir_records=[m['id'] for m in matches],admitted_edge=next((e for e in edges if e['from']==f and e['to']==t),None)))
put('NGB_CANDIDATES_RESOLVED.json',dict(complete=False,total=39,dispositions=dict(collections.Counter(c['disposition'] for c in resolved)),candidates=resolved))
# Exclusions are explicit candidates, not removed ledger rows.
exc=[]
program=lzma.open(Z/'LEAD_B006/aspis_r1_cost_probe_program.mir.xz','rt').read()
for name in ['accumulate','accumulate_with_node']:
 f='crates/aspis-r1-cost-probe/src/verifier.rs::'+name
 assert f not in closure(G,[root]);assert re.search(r'\b'+name+r'\b',program) is None
 refs=[]
 for d in D:
  if d['file'].startswith('crates/aspis-r1-cost-probe/'):
   refs += [dict(caller=d['function'],**c) for c in d['calls'] if c['expression']==name or c['expression'].endswith('::'+name)]
 exc.append(dict(function=f,disposition='REACHABILITY-EXCLUDED',entry_path=None,program_MIR_references=0,source_references=refs,reason='Only incoming library source chain is audit-only eight_way -> accumulate -> accumulate_with_node; neither appears in deployed program MIR or producer entry closure. Body presence in library MIR is not entry reachability.'))
put('NGB_EXCLUDED.json',dict(root=root,candidates=exc,removed_rows=[],cfg_evidence=dict(path='crates/aspis-r1-cost-probe/src/verifier.rs',revision=base['frozen_revision'],lines=[524,525,526,527,528],text='#[cfg(feature=\"audit-eight-way\")] #[path=\"eight_way.rs\"] pub mod eight_way;'),program_MIR=pin(Z/'LEAD_B006/aspis_r1_cost_probe_program.mir.xz')))
print(json.dumps(dict(admitted_edges=len(edges),new_rows=len(new_rows),total_rows=len(rows),new_functions=sorted(new_nodes),dispositions=collections.Counter(c['disposition'] for c in resolved))))
