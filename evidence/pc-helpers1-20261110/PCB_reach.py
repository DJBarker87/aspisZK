from pathlib import Path
import lzma,json,hashlib,collections
E=Path(__file__).resolve().parent;I=E.parent/'pool-inventory2-20261109'
g=json.load(lzma.open(I/'NKZ_GRAPH.json.xz'));inv=json.load(open(I/'NKZ_INVENTORY.json'));tract=json.load(open(I/'NKZ_TRACTABILITY.json'))['rows']
rows=[r for r in tract if r['class_']=='A' and r['genuinely_new'] and r['scope']=='ON_CONSERVATIVE_CLOSURE' and (r['function'].startswith('crates/aspis-core/') or (r['function'].startswith('crates/aspis-statement/') and '/pool_v1/' not in r['function']))];assert len(rows)==71
# Explicitly marked conservative/trait/function-item alternatives are cuts.
# UNIQUE_TYPED_OR_NAME remains ambiguous as to typed versus name-only resolution.
def cut(e):return any(t in e['kind'] for t in ['CONSERVATIVE','TRAIT_RECEIVER'])
adj=collections.defaultdict(list)
for e in g['edges']:
 if not e.get('conditional_dispatch_off',False):
  for t in e['targets']:adj[e['caller']].append((t,e))
def bfs(remove=False):
 prev={r:None for r in inv['roots']};q=collections.deque(prev)
 while q:
  u=q.popleft()
  for v,e in adj[u]:
   if remove and cut(e):continue
   if v not in prev:prev[v]=(u,e);q.append(v)
 return prev
allp=bfs();clean=bfs(True);out=[]
for r in rows:
 f=r['function'];path=[];cur=f
 if cur in allp:
  while allp[cur] is not None:
   u,e=allp[cur];path.append(dict(caller=u,target=cur,kind=e['kind'],artifact=e['artifact'],line=e['line'],callee_spelling=e.get('callee_spelling'),explicit_alternative=cut(e)));cur=u
  path.reverse()
 out.append(dict(row=r['row'],function=f,shortest_edge_count=len(path) if f in allp else None,on_root=cur if f in allp else None,shortest_chain=path,every_chain_has_explicit_conservative_or_trait_alternative=f not in clean,interpretation='YES' if f not in clean else 'NOT ESTABLISHED: graph has a route avoiding explicitly marked alternatives; UNIQUE_TYPED_OR_NAME is not evidence of resolved MIR calls',assessment_only=True))
assert all(r['shortest_edge_count'] is not None for r in out)
pins={n:hashlib.sha256((I/n).read_bytes()).hexdigest() for n in ['NKZ_GRAPH.json.xz','NKZ_INVENTORY.json','NKZ_TRACTABILITY.json']}
(E/'PCB_REACH.json').write_text(json.dumps(dict(inputs=pins,roots=inv['roots'],rows=out,proof_credit=False),indent=1)+'\n')
text=['# PCB scope assessment:71 other class-A rows','','Assessment only. This is a shortest-path query of the conservative NKZ graph, not a reachability proof, exclusion, or ownership transfer. No Lean scopes were used. Conditional-dispatch-OFF edges are omitted; all three recorded ON Pool roots are starts.','','YES means deleting every explicitly CONSERVATIVE/TRAIT_RECEIVER edge destroys all root-to-row paths. NOT ESTABLISHED means a path avoiding those labels exists; UNIQUE_TYPED_OR_NAME does not distinguish exact typed resolution from name-only association, so no resolved-MIR-only path is claimed. This reports all paths, not only the chosen shortest chain. Full edge artifacts, lines and spellings are in PCB_REACH.json.','','| Row | Edges | Every chain hits explicit alternative? | Shortest chain |','|---|---:|---|---|']
for r in out:
 chain=[r['on_root']]+[e['target'] for e in r['shortest_chain']]
 text.append('| '+r['row']+' | '+str(r['shortest_edge_count'])+' | '+('YES' if r['every_chain_has_explicit_conservative_or_trait_alternative'] else 'NOT ESTABLISHED')+' | '+' → '.join('`'+n+'`' for n in chain)+' |')
text+=['','Input hashes: '+json.dumps(pins,sort_keys=True)]
(E/'PCB_REACH.md').write_text('\n'.join(text)+'\n')
print('PCB scope assessment:71 shortest chains; '+str(sum(r['every_chain_has_explicit_conservative_or_trait_alternative'] for r in out))+' cut by explicit alternatives; no reachability credit')
