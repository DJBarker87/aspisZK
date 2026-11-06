"""NGB-style frozen AST + compiler MIR census with explicit conservative edges.
No proof credit. One Pool occurrence per source function (as TX1/TX2 in NGB),
with all observed generic instantiations attached, closures folded into owner.
"""
from pathlib import Path
import sys,json,lzma,subprocess,hashlib,re,collections
sys.dont_write_bytecode=True
sys.path.insert(0,'/private/tmp/NFZ-parser-20261104')
from tree_sitter import Language,Parser
import tree_sitter_rust
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';sha=lambda b:hashlib.sha256(b).hexdigest()
def git(p):return subprocess.check_output(['git','show',F+':'+p],cwd=R)
def put(n,d):
 raw=(json.dumps(d,indent=1,sort_keys=True)+'\n').encode()
 if len(raw)>20_000_000:
  (E/(n+'.xz')).write_bytes(lzma.compress(raw,preset=6));(E/(n+'.sha256')).write_text(sha(raw)+'\n');(E/n).unlink(missing_ok=True)
 else:(E/n).write_bytes(raw)
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def ancestors(n):
 while n.parent:n=n.parent;yield n
parser=Parser(Language(tree_sitter_rust.language()))
manifest=json.loads((E/'NKS_DEPLOYED_BUILD.json').read_text());paths=[x['path'] for x in manifest['compiler_input_checks'] if x['path'].endswith('.rs')]
D=[];sources={}
for p in paths:
 b=git(p);sources[p]=b;root=parser.parse(b).root_node;assert not root.has_error,p
 def txt(n):return b[n.start_byte:n.end_byte].decode() if n else ''
 for n in walk(root):
  if n.type!='function_item' or n.child_by_field_name('body') is None:continue
  scopes=[];impl=None;trait='';pars=list(ancestors(n))
  for a in reversed(pars):
   if a.type in ['mod_item','function_item','trait_item']:scopes.append(txt(a.child_by_field_name('name')))
   if a.type=='impl_item':scopes.append(txt(a.child_by_field_name('type')));impl=a;trait=txt(a.child_by_field_name('trait'))
  body=n.child_by_field_name('body');name=txt(n.child_by_field_name('name'));calls=[];refs=[]
  bindings=set()
  for q in walk(n):
   if q.type in ['parameter','let_declaration','for_expression']:
    pattern=q.child_by_field_name('pattern')
    if pattern:bindings.update(txt(x) for x in walk(pattern) if x.type=='identifier')
  for c in walk(body):
   if c.type=='call_expression':
    fn=c.child_by_field_name('function');args=c.child_by_field_name('arguments');calls.append(dict(line=c.start_point.row+1,expression=txt(fn),arguments=txt(args),function_item_arguments=[txt(a) for a in args.named_children if a.type in ['identifier','scoped_identifier'] and txt(a) not in bindings] if args else []))
   if c.type in ['identifier','scoped_identifier']:refs.append(dict(line=c.start_point.row+1,text=txt(c)))
  D.append(dict(function=p+'::'+'::'.join(scopes+[name]),file=p,name=name,trait=trait,start=n.start_point.row+1,end=n.end_point.row+1,impl_start=impl.start_point.row+1 if impl else None,body_range=[body.start_byte,body.end_byte],body_sha256=sha(b[body.start_byte:body.end_byte]),full_function_sha256=sha(b[n.start_byte:n.end_byte]),calls=calls,references=refs,mir_headers=[],mono_instances=[]))
bykey={d['function']:d for d in D};byname=collections.defaultdict(list)
for d in D:byname[d['name']].append(d)
def unparam(s):
 out='';depth=0
 for i,c in enumerate(s):
  if c=='<':depth+=1
  elif c=='>' and depth and (i==0 or s[i-1]!='-'):depth-=1
  elif not depth:out+=c
 return out.replace('::::','::').strip(':')
def method(s):return unparam(s).split('::')[-1].strip()
def module(d):
 x=d['file'].split('/src/')[-1].removesuffix('.rs').removesuffix('/mod')
 return '' if x=='lib' else x.replace('/','::')
def scope(d):return d['function'].split('::',1)[1].rsplit('::',1)[0] if '::' in d['function'].split('::',1)[1] else ''
def resolve(raw,crate=None,caller=None,emitted=True):
 raw=raw.strip().split(' as for<',1)[0];name=method(raw);cands=[d for d in byname.get(name,[]) if not emitted or d['mir_headers']]
 if crate:
  prefix={'aspis_pool':'programs/aspis-pool/','aspis_core':'crates/aspis-core/','aspis_statement':'crates/aspis-statement/'}[crate]
  cands=[d for d in cands if d['file'].startswith(prefix)]
 # Source/impl path provides authoritative header association.
 m=re.search(r'<impl at ([^:]+):(\d+):',raw)
 if m:
  exact=[d for d in cands if d['file']==m[1] and d['impl_start']==int(m[2])]
  return exact,'IMPL_SOURCE_LOCATION' if exact else 'DERIVED_OR_MACRO_IMPL'
 # Typed receiver/module disambiguation; retain all unresolved alternatives.
 simple=unparam(raw);parts=simple.split('::')[:-1]
 typed=re.match(r'<([^<>]+) as ',raw)
 if typed:
  ty=typed[1].split('::')[-1].strip('& ')
  exact=[d for d in cands if unparam(scope(d)).split('::')[-1]==ty]
  if exact:return exact,'TRAIT_RECEIVER'
 if parts:
  exact=[d for d in cands if scope(d) and unparam(scope(d)).split('::')[-1] in parts]
  if exact:cands=exact
  else:
   exact=[d for d in cands if module(d) and module(d).split('::')[-1] in parts]
   if exact:cands=exact
 if len(cands)>1 and caller and '::' not in simple:
  exact=[d for d in cands if d['file']==caller['file']]
  if exact:cands=exact
 return cands, 'UNIQUE_TYPED_OR_NAME' if len(cands)==1 else 'CONSERVATIVE_ALTERNATIVES' if cands else 'EXTERNAL_OR_UNRESOLVED'
# First pass associates every emitted body; nonlocal crate calls later resolve against union.
mirtexts={};header_records=[];blocks=[]
for crate in ['aspis_pool','aspis_core','aspis_statement']:
 s=lzma.decompress((E/('NKS_'+crate+'.mir.xz')).read_bytes()).decode();mirtexts[crate]=s
 lines=s.splitlines();active=None
 for i,l in enumerate(lines,1):
  if l.startswith('fn '):
   raw=l[3:].split('(')[0];closure=re.search(r'closure@([^:]+):(\d+):',l)
   if closure:
    ds=[d for d in D if d['file']==closure[1] and d['start']<=int(closure[2])<=d['end']]
    ds=sorted(ds,key=lambda d:d['end']-d['start'])[:1];kind='CLOSURE_IN_OWNER'
   else:ds,kind=resolve(raw,crate=crate,emitted=False)
   owner=ds[0] if len(ds)==1 else None;rec=dict(crate=crate,line=i,header=l,owner=owner['function'] if owner else None,association=kind)
   rec['conservative_owners']=[x['function'] for x in ds] if len(ds)>1 else []
   header_records.append(rec);active=dict(**rec,calls=[]);blocks.append(active)
   for candidate in ds:candidate['mir_headers'].append(dict(crate=crate,line=i,header=l,conservative_owner=len(ds)>1))
  inline=re.search(r'\(inlined (.*)\) \{',l)
  if active and inline:active['calls'].append(dict(line=i,callee=inline[1],text=l.strip(),inlined=True))
  if active and ' -> [' in l and ' = ' in l:
   expr=l.split(' = ',1)[1].split(' -> [',1)[0]
   # '(' nested inside a function-pointer type occurs inside angle brackets.
   depth=0;cut=len(expr)
   for j,c in enumerate(expr):
    if c=='<':depth+=1
    elif c=='>' and depth and (j==0 or expr[j-1]!='-'):depth-=1
    elif c=='(' and depth==0:cut=j;break
   active['calls'].append(dict(line=i,callee=expr[:cut],text=l.strip()))
# Explicit roots: all accepted spend/lifecycle dispatch branches, plus error/clear prefix.
rootspec=[
 ('AS8I','OFF','pair_forest.rs','process_pair_forest_initialize_with_runtime_v1','Creates master/lane state; initialization before a spend.'),
 ('AS8C','ON','pair_forest.rs','process_pair_forest_checkpoint_with_runtime_v1','Retains the authenticated forest checkpoint consumed by terminal settlement.'),
 ('AS8D','ON','pair_forest.rs','process_pair_forest_deposit_with_runtime_v1','Vault-backed deposit updates the forest used by the spend.'),
 ('ASQ8','ON','pair_forest.rs','process_pair_forest_terminal_v1','Deployed compact verifier-gated terminal, transfer/withdrawal continuation.'),
 ('ASF8','OFF','pair_forest.rs','process_pair_forest_terminal_full_asf8_v1','Full transport is cfg-disabled in pinned deployed features.'),
 ('ASIN','OFF','processor.rs','process_initialize_with_runtime_v1','Initializes legacy Pool accounts before a spend.'),
 ('ASDI','ON','processor.rs','process_deposit_with_runtime_v1','Legacy vault-backed deposit; conservatively retained deployed alternative.'),
 ('ASPP','ON','processor.rs','process_prepare_settlement_with_runtime_v1','Creates the retained prepared-settlement state.'),
 ('ASPX','ON','processor.rs','process_cancel_prepared_settlement_with_runtime_v1','Cancels/refunds a prepared settlement and closes its accounts.'),
 ('ASPF','ON','processor.rs','process_settle_prepared_with_runtime_v1','Consumes the prepared plan and persists settlement.'),
 ('ASJP','OFF','pair_processor.rs','process_pair_private_transfer_with_verifier_v1','pair-afterstate-evidence is cfg-disabled in deployed features.'),
 ('ASJW','OFF','pair_processor.rs','process_pair_withdrawal_with_verifier_v1','pair-afterstate-evidence is cfg-disabled in deployed features; held-site review retained separately.'),
 ('ASPT','ON','processor.rs','process_private_transfer_with_runtime_v1','Verifier-gated legacy private transfer; retained alternative.'),
 ('ASWD','ON','processor.rs','process_withdrawal_with_runtime_v1','Verifier-gated legacy withdrawal; retained alternative.')]
roots=[]
for magic,on,file,name,reason in rootspec:
 ds=[d for d in D if d['file']=='programs/aspis-pool/src/'+file and d['name']==name];assert len(ds)==1,(magic,ds)
 d=ds[0];roots.append(dict(magic=magic,classification=on,function=d['function'],reason=reason,source_line=d['start'],emitted_in_sbf_MIR=bool(d['mir_headers'])))
entry='programs/aspis-pool/src/processor.rs::process_instruction';onroots={x['function'] for x in roots if x['classification']=='ON'};offroots={x['function'] for x in roots if x['classification']=='OFF'}
edges=[]
for block in blocks:
 for ownerkey in ([block['owner']] if block['owner'] else block['conservative_owners']):
  d=bykey[ownerkey]
  for c in block['calls']:
   ds,kind=resolve(c['callee'],caller=d)
   # SDK/external explicit namespace cannot become a project body by shared name.
   external=bool(re.match(r'(?:<)?(?:core|std|alloc|solana_\w+|borsh|hashbrown|sha2|curve25519_dalek|program|Clock|Rent|AccountInfo|Pubkey)::',c['callee']))
   if external:ds=[];kind='SDK_STD_OR_EXTERNAL'
   if c.get('inlined'):kind='MIR_INLINED_SCOPE:'+kind
   if d['function']==entry:
    direct_names={re.split(r'[.:]',a['expression'])[-1] for a in d['calls']}|{'from'}
    ds=[x for x in ds if x['name'] in direct_names]
   edges.append(dict(caller=d['function'],callee_spelling=c['callee'],targets=sorted(x['function'] for x in ds),kind=kind,artifact='NKS_'+block['crate']+'.mir.xz',line=c['line'],text=c['text'],header=block['header'],conditional_dispatch_off=d['function']==entry and any(x['function'] in offroots for x in ds)))
# Function items embedded as arguments/trait callbacks are not a direct call opcode.
# Bind known source references, then keep generic indirect/trait call opcode too.
for d in D:
 if not d['mir_headers']:continue
 for c in d['calls']:
  for token in sorted(set(c['function_item_arguments'])):
   ds,kind=resolve(token,caller=d)
   # Only distinctive named functions; never pretend bare variables are function items.
   if not ds or token in ['new','default','get','clone','into','from','id']:continue
   if not any(x['name'] in token and len(x['name'])>5 for x in ds):continue
   edges.append(dict(caller=d['function'],callee_spelling=token,targets=sorted(x['function'] for x in ds),kind='AST_FUNCTION_ITEM_CONSERVATIVE',artifact=d['file'],line=c['line'],text=c['arguments'],header=None,conditional_dispatch_off=d['function']==entry and any(x['function'] in offroots for x in ds)))
# Mono items: preserve every emitted instance, not just names of generic source bodies.
mono=[]
for crate in mirtexts:
 for i,l in enumerate((E/('NKS_'+crate+'.mono.txt')).read_text().splitlines(),1):
  if not l.startswith('MONO_ITEM fn '):continue
  name=l[len('MONO_ITEM fn '):].split(' @@ ')[0];ds,kind=resolve(name,crate=None)
  if re.match(r'(?:<)?(?:core|std|alloc|solana_\w+|borsh|hashbrown|sha2|curve25519_dalek|program|Clock|Rent|AccountInfo|Pubkey)::',name):ds=[]
  rec=dict(crate=crate,line=i,instance=name,targets=sorted(x['function'] for x in ds),association=kind);mono.append(rec)
  for d in ds:d['mono_instances'].append(rec)
# Monomorphized function-item arguments bind concrete Fn/trait instances.
for item in mono:
 for ownerkey in item['targets']:
  for token in re.findall(r'\{([^{}]+)\}',item['instance']):
   ds,kind=resolve(token,caller=bykey[ownerkey])
   if not ds:continue
   edges.append(dict(caller=ownerkey,callee_spelling=token,targets=sorted(x['function'] for x in ds),kind='MONO_FUNCTION_ITEM',artifact='NKS_'+item['crate']+'.mono.txt',line=item['line'],text=item['instance'],header=None,conditional_dispatch_off=ownerkey==entry and any(x['function'] in offroots for x in ds)))
G=collections.defaultdict(set)
for e in edges:
 if not e['conditional_dispatch_off']:G[e['caller']].update(e['targets'])
seen={entry}|onroots;queue=collections.deque(sorted(seen));parent={x:None for x in seen}
while queue:
 f=queue.popleft()
 for c in sorted(G[f]):
  if c not in seen:seen.add(c);parent[c]=f;queue.append(c)
ledger=json.loads(lzma.open(R/'evidence/ledger19-20261108/NKN_LEDGER.json.xz').read());old=collections.defaultdict(list)
for row in ledger['rows']:old[row['function']].append(row)
rows=[]
for i,key in enumerate(sorted(seen),1):
 d=bykey[key];matches=[x for x in old[key] if x['frozen_body_sha256']==d['body_sha256']];mismatch=[x['row'] for x in old[key] if x['frozen_body_sha256']!=d['body_sha256']]
 # A frozen body equality is a reusable law candidate, never a new caller-domain certificate.
 rows.append(dict(id=f'POOL:{i:03}',function=key,frozen_body_sha256=d['body_sha256'],full_function_sha256=d['full_function_sha256'],source_file=d['file'],source_lines=[d['start'],d['end']],callees=sorted(G[key]),edges=[e for e in edges if e['caller']==key],mir_headers=d['mir_headers'],monomorphized_instances=d['mono_instances'],basis_overlap=[dict(row=x['row'],status=x['status'],obligation_statement_hash=x.get('obligation_statement_hash'),owner_module=x.get('owner_module'),evidence_dir=x.get('evidence_dir')) for x in matches],basis_hash_disagreements=mismatch,genuinely_new=not bool(matches),inventory_status='INVENTORY_ONLY_NO_CREDIT',scope='ON_CONSERVATIVE_CLOSURE',predecessor=parent[key]))
# Number OFF owners explicitly for review; these are NOT counted as ON closure.
owner_review=json.loads((R/'evidence/pool-borrow3-20261107/NIZ_OPEN_SITES.json').read_text())['owners']
off_review=[]
for key in sorted({x['function'] for x in owner_review}-seen):
 d=bykey[key];off_review.append(dict(id=f'POOL:{len(rows)+len(off_review)+1:03}',function=key,frozen_body_sha256=d['body_sha256'],full_function_sha256=d['full_function_sha256'],source_file=d['file'],source_lines=[d['start'],d['end']],callees=sorted(G[key]),mir_headers=d['mir_headers'],monomorphized_instances=d['mono_instances'],scope='OFF_REVIEW_NOT_ON_CLOSURE',genuinely_new=None,basis_overlap=[],inventory_status='INVENTORY_ONLY_NO_CREDIT',edges=[e for e in edges if e['caller']==key],reason='Exclusive-guard owner retained for review; reached only from OFF initialization/cfg-disabled instruction in this compiler-backed union. No native production exclusion proof is claimed.'))
put('NKS_ROOTS.json',dict(entrypoint='SDK entrypoint! -> processor::process_instruction',entry=entry,roots=roots,invalid_magic='Err(InvalidInstructionData); return-data cleared initially and on error',non_dispatch_admin='No registry-maintenance/admin/standalone-close dispatch branch in Pool; close_program_account_v1 is an ON cancel/settle callee, not an OFF instruction.',scope='Conservative union of all deployed spend/lifecycle alternatives; not a claim each instruction occurs in one two-transaction trace. AS8C included conservatively as checkpoint preparation.'))
# Full graph and unmatched headers are retained so candidate boundaries remain reviewable.
put('NKS_GRAPH.json',dict(headers=header_records,edges=edges,monomorphized_instances=mono,unmatched_headers=[h for h in header_records if not h['owner']],entry_dispatch_exclusions=[e for e in edges if e['conditional_dispatch_off']]))
put('NKS_INVENTORY.json',dict(schema='NKS-Pool-inventory-v1',frozen_revision=F,pool_elf_sha256='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548',security_target_established=False,proof_credit=0,method='NGB-style AST hashes plus deployed SBF MIR calls and inlined scopes, source callback overlay, conservative typed/name alternatives, emitted mono-instance census; SDK/std remain explicit boundary calls under retained trust.',occurrence_semantics='One occurrence per frozen source function in Pool root-union context; all emitted generic instances attached. Closures folded into source owner. Conservative alternatives do not establish physical reachability.',roots=sorted(onroots),rows=rows,off_review_rows=off_review,counts=dict(rows=len(rows),genuinely_new=sum(r['genuinely_new'] for r in rows),shared_body_occurrences=sum(not r['genuinely_new'] for r in rows),basis_rows_matched=len({x['row'] for r in rows for x in r['basis_overlap']})),limits=['MIR is human-readable compiler diagnostics, not a formally verified callgraph.', 'Generic/name alternatives are retained, not silently chosen. Unresolved SDK/std/indirect calls are listed in boundary inventory.', 'Shared body closure does not transfer caller-domain or feature-dependent cohort association.', 'No native proof, ledger edit, trust addition, row promotion or security conclusion.']))
# Source AST for reproduction, stripped of redundant identifier text.
ast=[{k:v for k,v in d.items() if k not in ['references','mir_headers','mono_instances']} for d in D]
raw=(json.dumps(ast,sort_keys=True,indent=1)+'\n').encode();(E/'NKS_SOURCE_AST.json.xz').write_bytes(lzma.compress(raw));(E/'NKS_SOURCE_AST.json.sha256').write_text(sha(raw)+'\n')
print('NKS inventory '+json.dumps(dict(rows=len(rows),new=sum(r['genuinely_new'] for r in rows),shared=sum(not r['genuinely_new'] for r in rows),unmatched_headers=sum(not h['owner'] for h in header_records))))
