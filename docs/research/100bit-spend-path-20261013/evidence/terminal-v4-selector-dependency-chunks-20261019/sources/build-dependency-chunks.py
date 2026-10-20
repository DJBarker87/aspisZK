from pathlib import Path
import re,json,hashlib,sys
src=Path('/tmp/terminal-v4-model-sources-20261019/AspisR1SelectedMaskProbe/Funs.lean'); target=sys.argv[1]; prefix=sys.argv[2]
s=src.read_text(); lines=s.splitlines(keepends=True); key=r'(?:def|abbrev|opaque|theorem|instance|impl_def|inductive|structure|class|axiom|constant)'
starts=[]
for i,l in enumerate(lines):
 if re.match(r'^'+key+r'\b',l): starts.append(i)
 elif l.startswith('@['):
  for k in range(i,min(i+9,len(lines))):
   if re.match(r'^'+key+r'\b',lines[k]) or re.search(r'\]\s*'+key+r'\b',lines[k]): starts.append(i); break
starts=sorted(set(starts)); raw=[]
for j,st in enumerate(starts):
 en=starts[j+1] if j+1<len(starts) else len(lines); head=''.join(lines[st:min(st+10,en)]); m=re.search(r'\b'+key+r'\s+([^\s(:]+)',head,re.M)
 if m: raw.append({'name':m.group(1),'st':st,'en':en,'body':''.join(lines[st:en])})
by={x['name']:x for x in raw}; names=sorted(by,key=len,reverse=True); refs={x['name']:set(n for n in names if n!=x['name'] and re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w.])',x['body'])) for x in raw}
def closure(t):
 seen=set();todo=[t]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(refs.get(n,())-seen)
 return seen
wanted=closure(target); base=closure('pool_v1.pair_forest_copy_terminal.Selectors.active')
extra=[x for x in raw if x['name'] in wanted-base]
# Each decl starts at its nearest doc; ends at next declaration's nearest doc, keeping source bytes unchanged.
for x in extra:
 st=x['st']; x['doc']=st
 for k in range(st-1,19,-1):
  if lines[k].lstrip().startswith('/--'): x['doc']=k;break
  if re.match(r'^'+key+r'\b',lines[k]):break
  if lines[k].startswith('@['):continue
 nxt=next((y for y in raw if y['st']>st),None); end=nxt['st'] if nxt else len(lines)
 if nxt:
  for k in range(nxt['st']-1,st,-1):
   if lines[k].lstrip().startswith('/--'):end=k;break
 x['enddoc']=end; x['text']=''.join(lines[x['doc']:end]);x['bytes']=len(x['text'].encode());x['sha']=hashlib.sha256(x['text'].encode()).hexdigest()
# chunks with max 12000 declaration bytes, preserving source order
chunks=[];cur=[];size=0
for x in extra:
 if cur and size+x['bytes']>12000: chunks.append(cur);cur=[];size=0
 cur.append(x);size+=x['bytes']
if cur:chunks.append(cur)
header=''.join(lines[:20]).replace('import AspisR1SelectedMaskProbe.FunsExternal\n','import AspisR1SelectedMaskProbe.FunsExternal\nimport TerminalV4ActiveSelectionBridgeV1\n')
prev='TerminalV4ActiveSelectionBridgeV1'; manifest={'generated_funs_source':str(src),'generated_funs_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'root_target':target,'target_closure_count':len(wanted),'prior_active_module':'TerminalV4ActiveSelectionBridgeV1','prior_closure_count':len(base),'new_decl_count':len(extra),'new_decl_bytes':sum(x['bytes'] for x in extra),'chunk_max_decl_bytes':12000,'chunks':[]}
for i,chunk in enumerate(chunks,1):
 module=f'{prefix}{i:02d}'; out=Path(f'/tmp/{module}.lean'); h=header
 if i>1:
  h=h.replace('import TerminalV4ActiveSelectionBridgeV1\n',f'import TerminalV4ActiveSelectionBridgeV1\nimport {prefix}{i-1:02d}\n')
 body=''.join(x['text'] for x in chunk)
 final=(i==len(chunks))
 code=h+body+(f'\nend AspisR1SelectedMaskProbe\n\n#print axioms AspisR1SelectedMaskProbe.{target}\n' if final else '\nend AspisR1SelectedMaskProbe\n')
 out.write_text(code); manifest['chunks'].append({'module':module,'path':str(out),'sha256':hashlib.sha256(code.encode()).hexdigest(),'bytes':len(code.encode()),'decls':[{'name':x['name'],'start_line':x['doc']+1,'end_line_exclusive':x['enddoc']+1,'source_block_sha256':x['sha']} for x in chunk]});prev=module
Path(f'/tmp/{prefix}manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k] for k in ('generated_funs_sha256','root_target','target_closure_count','prior_closure_count','new_decl_count','new_decl_bytes')},indent=2));
for c in manifest['chunks']: print(c['module'],c['bytes'],len(c['decls']),[d['name'] for d in c['decls']])
