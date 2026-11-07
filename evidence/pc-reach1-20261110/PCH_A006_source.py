"""Compiler-instance supergraph. Unknown edges are universal, never exclusion evidence.
LLVM gives resolved emitted instances; MIR retains calls, inlining, drops and materialisation.
This deliberately refuses to turn a source-name association into a resolved instance edge.
"""
import pathlib,json,lzma,hashlib,re,collections,sys,shutil
B=pathlib.Path(__file__).resolve().parent;sha=lambda x:hashlib.sha256(x).hexdigest()
I=json.loads(lzma.decompress((B/'PCH_GRAPH_INPUT.json.xz').read_bytes()));assert I['authority']['admitted'];assert shutil.disk_usage(B).free>=40_000_000_000
A=I['ast'];rows=[r for r in I['rows'] if r['genuinely_new'] and r['scope']=='ON_CONSERVATIVE_CLOSURE'];assert len(rows)==278
N={};edges=[];pins={};mirsites=[];global_records=[];mono=[]
def norm(x):
 # Erase type arguments for association only, never for an exact call verdict.
 out='';dep=0
 for i,c in enumerate(x):
  if c=='<':dep+=1
  elif c=='>' and dep and (i==0 or x[i-1]!='-'):dep-=1
  elif not dep:out+=c
 return out.replace('::::','::').strip(':')
def expected(d):
 crate='aspis_pool' if d['file'].startswith('programs/') else d['file'].split('/')[1].replace('-','_')
 mod=d['file'].split('/src/')[-1].removesuffix('.rs').removesuffix('/mod').replace('/','::')
 return norm('::'.join([crate]+([] if mod=='lib' else [mod])+[d['function'].split('::',1)[1]]))
bysp=collections.defaultdict(list)
for d in A:bysp[expected(d)].append(d['function'])
refs=lambda line:re.findall(r'@("(?:[^"\\]|\\.)+"|[-\w.$]+)',line)
def add(src,dst,kind,artifact,line,text,**extra):
 edges.append(dict(source=src,target=dst,kind=kind,artifact=artifact,line=line,text=text,**extra))
texts={};llfiles=[]
for c,stem in [('aspis_pool','PCH_B003_aspis_pool'),('aspis_core','PCH_B002_aspis_core-268c35f57b2871a4'),('aspis_statement','PCH_B002_aspis_statement-619c698a69debaf8')]:
 for ext in ['mir','ll']:
  p=B/(stem+'.'+ext+'.xz');raw=lzma.decompress(p.read_bytes()) if p.exists() else (B/('PCH_B003' if c=='aspis_pool' else 'PCH_B002')/(('aspis_pool' if c=='aspis_pool' else stem.split('PCH_B002_')[1])+'.'+ext)).read_bytes()
  pins[p.name]=dict(sha256=sha(lzma.compress(raw)) if not p.exists() else sha(p.read_bytes()),uncompressed_sha256=sha(raw),bytes=len(raw));texts[(c,ext)]=raw.decode()
  if ext=='ll':llfiles.append((c,p.name,raw.decode()))
 # Retain every mono instance exactly as rustc printed it.
 p=B/('PCH_B003/compiler.stdout' if c=='aspis_pool' else 'PCH_B002/'+c+'.stdout')
 for lineno,line in enumerate(p.read_text().splitlines(),1):
  if line.startswith('MONO_ITEM '):mono.append(dict(crate=c,line=lineno,text=line,instance=line.split(' @@ ')[0].removeprefix('MONO_ITEM fn '),artifact=('PCH_B003_compiler.stdout.xz' if c=='aspis_pool' else 'PCH_B002_'+c+'.stdout.xz')))
# Full MIR site census, including sites outside the original three ON roots.
for (c,ext),s in texts.items():
 if ext!='mir':continue
 active=None;head=None
 artifact=next(n for n in pins if c in n and '.mir.' in n)
 for lineno,line in enumerate(s.splitlines(),1):
  if line.startswith('fn '):
   active='mir:'+c+':'+str(lineno);head=line
   N[active]=dict(kind='MIR_TEMPLATE_NOT_RESOLVED_INSTANCE',header=line,artifact=artifact,line=lineno)
  if not active:continue
  kind=None
  if '(inlined ' in line:kind='MIR_INLINED_SCOPE'
  elif ' -> [' in line and (' = ' in line or 'drop(' in line):kind='MIR_DROP' if 'drop(' in line else 'MIR_CALL'
  elif any(x in line for x in ['ReifyFnPointer','ClosureFnPointer','PointerCoercion','closure@']):kind='MIR_FN_POINTER_OR_CLOSURE_MATERIALISATION'
  if kind:
   site='site:'+c+':'+str(lineno);N[site]=dict(kind=kind,artifact=artifact,line=lineno,text=line.strip(),caller=active)
   add(active,site,kind,artifact,lineno,line.strip(),resolved=False)
   # No guessing instantiation of generic MIR or erased pointer types.
   add(site,'PCH_UNKNOWN',kind+'_UNRESOLVED',artifact,lineno,line.strip(),resolved=False,expansion='EVERY_SOURCE_AND_COMPILER_INSTANCE; type compatibility unavailable, universal superset')
   mirsites.append(dict(id=site,caller=active,kind=kind,artifact=artifact,line=lineno,text=line.strip(),header=head))
# LLVM symbol definitions/references are resolved by exact mangled identity.
for c,artifact,s in llfiles:
 active=None;comment=''
 for lineno,line in enumerate(s.splitlines(),1):
  if line.startswith('; ') and not line.startswith('; Function Attrs:'):comment=line[2:]
  if line.startswith(('define ','declare ')):
   rr=refs(line)
   if not rr:continue
   sym=rr[0];key='llvm:'+sym;defined=line.startswith('define ')
   d=N.setdefault(key,dict(kind='LLVM_INSTANCE',symbol=sym,definitions=[],declarations=[],source_functions=[]))
   d['definitions' if defined else 'declarations'].append(dict(crate=c,artifact=artifact,line=lineno,text=line,demangled=comment))
   for source in bysp.get(norm(comment),[]):
    if source not in d['source_functions']:d['source_functions'].append(source)
   active=key if defined else None;continue
  if line.startswith('@'):
   rr=refs(line)
   if rr:
    key='global:'+rr[0];N.setdefault(key,dict(kind='LLVM_GLOBAL',artifact=artifact,line=lineno,text=line));global_records.append(dict(id=key,artifact=artifact,line=lineno,text=line))
    for sym in rr[1:]:add(key,'llvm:'+sym,('VTABLE_MATERIALISATION' if 'vtable' in rr[0] else 'GLOBAL_FUNCTION_REFERENCE'),artifact,lineno,line,resolved=True)
   continue
  if active:
   rr=refs(line)
   if re.search(r'\b(call|invoke|callbr)\b',line):
    # All referenced symbols retained; references not resolving to definitions are external boundaries.
    for sym in rr:add(active,'llvm:'+sym,'LLVM_DIRECT_OR_INTRINSIC',artifact,lineno,line.strip(),resolved=True)
    # Indirect calls have a %callee immediately before an argument list.
    if re.search(r'\b(?:call|invoke|callbr)\b.*?%[-\w.]+\(',line):add(active,'PCH_UNKNOWN','LLVM_INDIRECT_UNRESOLVED',artifact,lineno,line.strip(),resolved=False,expansion='ALL type-compatible instances; universal superset used')
   else:
    for sym in rr:add(active,'llvm:'+sym,'LLVM_FUNCTION_OR_GLOBAL_MATERIALISATION',artifact,lineno,line.strip(),resolved=True)
   if line=='}':active=None
# Undefined symbols, runtime/library/allocator/abort boundaries are kept, not assumed leaf.
for e in list(edges):
 if e['target'].startswith('llvm:') and e['target'] not in N:
  g='global:'+e['target'][5:]
  if g in N:e['target']=g
  else:N[e['target']]=dict(kind='LLVM_EXTERNAL_OR_ALIAS',symbol=e['target'][5:])
for key,d in list(N.items()):
 if d['kind'].startswith('LLVM') and d['kind']!='LLVM_GLOBAL' and not d.get('definitions'):
  add(key,'PCH_UNKNOWN','EXTERNAL_UNRESOLVED',d.get('declarations',[{}])[0].get('artifact','compiler boundary'),d.get('declarations',[{}])[0].get('line',0),d.get('symbol',''),resolved=False,expansion='Universal superset; no external omitted')
N['PCH_UNKNOWN']=dict(kind='UNRESOLVED_UNIVERSAL',rule='c-g(5)',expands_to='ALL source rows and all compiled instances; conservative fallback, no type exclusions')
for r in rows:N['row:'+r['row']]=dict(kind='SOURCE_OCCURRENCE',function=r['function'])
# This explicit unresolved super-edge is why missing source-name/codegen matches cannot justify exclusion.
for key in sorted(N):
 if key!='PCH_UNKNOWN':add('PCH_UNKNOWN',key,'UNRESOLVED_UNIVERSAL_TARGET','c-g(5)',0,'unknown target includes this candidate',resolved=False)
roots=[]
for key,d in N.items():
 if d['kind']!='LLVM_INSTANCE':continue
 name=d.get('symbol','').strip('"');comments=[x['demangled'] for x in d.get('definitions',[])]
 if name in ['entrypoint','custom_panic','abort','__rust_alloc','__rust_dealloc','__rust_realloc','__rust_alloc_zeroed','__rust_alloc_error_handler'] or 'aspis_pool::processor::process_instruction' in comments:
  roots.append(dict(instance=key,reason='deployed entrypoint/process_instruction/panic/abort/global allocator',certain=True))
# Runtime handler roots not defined in the three project modules have explicit unknown edges.
for name in ['abort','__rust_alloc','__rust_dealloc','__rust_realloc','__rust_alloc_zeroed','__rust_alloc_error_handler']:
 key='runtime-root:'+name;N[key]=dict(kind='RUNTIME_HANDLER_ROOT',name=name);roots.append(dict(instance=key,reason='c-g(7): handler boundary; implementation outside three project IR modules',certain=False));add(key,'PCH_UNKNOWN','RUNTIME_HANDLER_UNRESOLVED','c-g(7)',0,name,resolved=False)
# Record every dispatched tag from the compiled process MIR (not the three old ON starts).
process=[m for m in N.values() if m.get('kind')=='MIR_TEMPLATE_NOT_RESOLVED_INSTANCE' and m['artifact'].startswith('PCH_B003_') and m['header'].startswith('fn process_instruction(')]
assert len(process)==1
sources=json.loads(lzma.decompress((B/'PCH_FROZEN.json.xz').read_bytes()));processor=sources['programs/aspis-pool/src/processor.rs']
dispatch=[dict(line=i,text=l.strip()) for i,l in enumerate(processor.splitlines(),1) if 'b"AS' in l]
# Every tag is reached through process_instruction; no cfg-disabled exclusion is inferred.
# Compute shortest resolved instance chains, separately from paths using unknown edges.
def bfs(resolved_only):
 adj=collections.defaultdict(list)
 for i,e in enumerate(edges):
  if not resolved_only or e.get('resolved'):adj[e['source']].append((e['target'],i))
 q=collections.deque(r['instance'] for r in roots if not resolved_only or r['certain']);prev={k:None for k in q}
 while q:
  u=q.popleft()
  for v,i in adj[u]:
   if v not in prev:prev[v]=(u,i);q.append(v)
 return prev
exact=bfs(True);allpaths=bfs(False)
def chain(key,prev):
 result=[]
 while prev.get(key) is not None:
  u,i=prev[key];result.append(i);key=u
 return list(reversed(result))
verdicts=[]
for r in rows:
 key='row:'+r['row'];matches=[k for k,d in N.items() if r['function'] in d.get('source_functions',[])]
 resolved=[k for k in matches if k in exact]
 # LLVM is authoritative codegen, but the requested MIR instance association is not supplied by name-erasure.
 # With zero Kani/Lean this is an audit dependency, never a source body claim.
 v=dict(row=r['row'],function=r['function'],class_=r['class_'],inherited_status=I['status'][r['row']],verdict='UNRESOLVED',reason='c-g(5)/(7): reachable unresolved runtime/indirect/template association; no exclusion may use this path.',codegen_matches=matches,codegen_cross_check=dict(artifact_pins=pins,present=bool(matches),absence_established=False),resolved_codegen_witness=chain(min(resolved,key=lambda k:len(chain(k,exact))),exact) if resolved else None,unresolved_witness=chain(key,allpaths),caller_MIR_instances_resolved=False)
 verdicts.append(v)
for i,e in enumerate(edges):e['id']=i
out=dict(schema='PCH-INSTANCE-SUPERGRAPH-2',authority='PCH_AUTHORITY.json',elf_sha256=I['authority']['retained_elf_hash_comparison']['fresh_ELF_hash'],pins=pins,nodes=N,edges=edges,roots=roots,dispatch_tags=dispatch,process_mir=process[0],mir_sites=mirsites,monomorphized_instances=mono,limitations=['MIR templates are retained separately from resolved LLVM instances; template-to-instance association is OPEN, never inferred by a method name.','Unknown externals/indirect calls/handler roots universally include every candidate; this is deliberately too broad for any exclusion.','No standalone pre-strip IR for SDK/std runtime handlers was retained in the permitted source corpus. No authority is inferred from native MIR.'],counts=dict(nodes=len(N),edges=len(edges),mono=len(mono),mir_sites=len(mirsites),roots=len(roots),resolved_reachable_instances=len(exact)))
raw=(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n').encode();(B/'PCH_GRAPH.json.xz').write_bytes(lzma.compress(raw));(B/'PCH_GRAPH.json.sha256').write_text(sha(raw)+'\n')
(B/'PCH_VERDICTS.json').write_text(json.dumps(dict(schema='PCH-VERDICTS-2',rows=verdicts,authority='PCH_AUTHORITY.json',not_a_body_proof=True),indent=1)+'\n')
(B/'PCH_GRAPH_SUMMARY.json').write_text(json.dumps(dict(counts=out['counts'],verdicts=dict(collections.Counter(v['verdict'] for v in verdicts)),exclusions=0,graph_sha256=sha(raw)),indent=1))
# Any observation about non-new/shared rows is routed to A, never an exclusion.
shared=[dict(row=r['id'],function=r['function'],disposition='NO EXCLUSION OR STATUS CHANGE; unresolved supergraph affects shared-body reachability too',codegen_matches=[k for k,d in N.items() if r['function'] in d.get('source_functions',[])]) for r in I['inventory']['rows'] if not r['genuinely_new']]
(B/'PCH_SHARED_FOR_STREAM_A.json').write_text(json.dumps(dict(status='OBSERVATIONS_ONLY_NOT_EXCLUSIONS',rows=shared),indent=1))
print('PCH graph: '+json.dumps(out['counts'])+'; all 278 rows UNRESOLVED; no exclusions')
