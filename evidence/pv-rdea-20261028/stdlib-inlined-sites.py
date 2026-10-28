from pathlib import Path
import re,json,lzma,subprocess,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');B=(D/'client-deployed-baseline') if (D/'client-deployed-baseline').exists() else (D/'client-target/release/devnet_spend')
raw=subprocess.check_output(['nm','--defined-only',str(B)],text=True)
dem=subprocess.check_output(['nm','-C','--defined-only',str(B)],text=True)
byaddr={}
for line in dem.splitlines():
 x=line.split(maxsplit=2)
 if len(x)==3:byaddr[x[0]]=x[2]
linked={};addresses={}
for line in raw.splitlines():
 x=line.split(maxsplit=2)
 if len(x)==3:linked[x[2]]=byaddr.get(x[0],x[2]);addresses[x[2]]=x[0]
rows=[];modules=[]
for p in sorted((D/'stdlib-ir').glob('*.ll.xz')):
 src=lzma.decompress(p.read_bytes()).decode();lines=src.splitlines();nodes={}
 for line in lines:
  m=re.match(r'^!(\d+) = (.*)',line)
  if m:nodes[int(m[1])]=m[2]
 def ref(node,key):
  m=re.search(r'\b'+key+r': !(\d+)',node);return int(m[1]) if m else None
 def field(node,key):
  m=re.search(r'\b'+key+r': "((?:[^"\\]|\\.)*)"',node);return m[1] if m else None
 def program(scope):
  seen=set()
  while scope is not None and scope not in seen:
   seen.add(scope);node=nodes.get(scope,'')
   if '!DISubprogram(' in node:return scope
   scope=ref(node,'scope')
  return None
 def location(loc):
  node=nodes.get(loc,'');s=program(ref(node,'scope'));pr=nodes.get(s,'');fil=nodes.get(ref(pr,'file'),'')
  f=field(fil,'filename');directory=field(fil,'directory');lm=re.search(r'\bline: (\d+)',node);cm=re.search(r'\bcolumn: (\d+)',node)
  return dict(file=f,directory=directory,line=int(lm[1]) if lm else None,column=int(cm[1]) if cm else None,scope=s,program_name=field(pr,'name'),linkage=field(pr,'linkageName'))
 targets={}
 for i,node in nodes.items():
  if '!DISubprogram(' not in node:continue
  n=field(node,'name');f=field(nodes.get(ref(node,'file'),''),'filename') or ''
  if n in ['with_capacity','reserve_exact'] and (f.endswith('/string.rs') or f=='string.rs'):
   targets[i]='V181/String::'+n
  if n in ['join','_join','push','_push'] and (f.endswith('/path.rs') or f=='path.rs'):
   targets[i]='V178/Path::'+n
 current=None;seenkeys=set();count=0
 for no,line in enumerate(lines,1):
  if line.startswith('define '):
   m=re.search(r'@("[^"\n]+"|[-A-Za-z$._0-9]+)\(',line);current=m[1].strip('"') if m else None
  if current and current in linked:
   lm=re.search(r'!dbg !(\d+)',line)
   if lm and not line.startswith('define '):
    loc=int(lm[1]);visited=set()
    while loc is not None and loc not in visited:
     visited.add(loc);node=nodes.get(loc,'');s=program(ref(node,'scope'));parent=ref(node,'inlinedAt')
     if s in targets and parent is not None:
      at=location(parent);chain=[];cursor=parent;walked=set()
      while cursor is not None and cursor not in walked:
       walked.add(cursor);chain.append(location(cursor));cursor=ref(nodes.get(cursor,''),'inlinedAt')
      origin=next((x for x in chain if not (x['program_name'] or '').startswith(('push<','join<'))),at)
      key=(current,targets[s],tuple((x['file'],x['line'],x['column'],x['linkage']) for x in chain))
      if key not in seenkeys:
       seenkeys.add(key);rows.append(dict(module=p.name,function=current,demangled=linked[current],function_address=addresses[current],target=targets[s],callsite=at,source_origin=origin,inline_chain=chain,instruction=line.strip(),ir_line=no))
     loc=parent
  if current and line.startswith('}'):current=None
 modules.append(dict(path=str(p),ir_sha256=hashlib.sha256(src.encode()).hexdigest(),target_debug_subprograms=len(targets),debug_nodes=len(nodes)))
result=dict(binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),class_='Compiler-emitted inline debug metadata from the exact rustc1.94.1 installed std/alloc bitcode; restricted to functions present in the linked client. A conservative site inventory, not proof that each source branch executes.',modules=modules,sites=rows)
(D/'stdlib-inlined-sites-v2.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(rows,indent=2))
