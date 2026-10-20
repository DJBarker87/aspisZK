from pathlib import Path
import re,json,hashlib,sys
src=Path('/tmp/terminal-v4-model-sources-20261019/AspisR1SelectedMaskProbe/Funs.lean'); target=sys.argv[1]; version=sys.argv[2]
s=src.read_text(); lines=s.splitlines(keepends=True); key=r'(?:def|abbrev|opaque|theorem|instance|impl_def|inductive|structure|class|axiom|constant)'
starts=[]
for i,line in enumerate(lines):
 if re.match(r'^'+key+r'\b',line): starts.append(i)
 elif line.startswith('@['):
  for k in range(i,min(i+9,len(lines))):
   if re.match(r'^'+key+r'\b',lines[k]) or re.search(r'\]\s*'+key+r'\b',lines[k]): starts.append(i); break
starts=sorted(set(starts)); raw=[]
for j,st in enumerate(starts):
 en=starts[j+1] if j+1<len(starts) else len(lines); head=''.join(lines[st:min(st+10,en)]); m=re.search(r'\b'+key+r'\s+([^\s(:]+)',head,re.M)
 if m: raw.append({'name':m.group(1),'st':st,'en':en,'body':''.join(lines[st:en])})
by={x['name']:x for x in raw}; names=sorted(by,key=len,reverse=True); refs={x['name']:set(n for n in names if n!=x['name'] and re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w.])',x['body'])) for x in raw}
if target not in by: raise SystemExit('target missing: '+target)
seen=set(); todo=[target]
while todo:
 n=todo.pop()
 if n in seen: continue
 seen.add(n); todo.extend(q for q in refs.get(n,()) if q not in seen)
ordered=[x for x in raw if x['name'] in seen]
# Attach preceding doc comments/attributes; the declaration body extends to the next top-level declaration marker.
for i,x in enumerate(ordered):
 st=x['st']; doc=st
 for k in range(st-1,19,-1):
  if lines[k].lstrip().startswith('/--'): doc=k; break
  if re.match(r'^'+key+r'\b',lines[k]): break
  if lines[k].startswith('@['): continue
 next_decl=next((y['st'] for y in raw if y['st']>st),len(lines))
 # End before the next declaration's doc opener, using nearest doc in source between current body and next declaration.
 nxt=next((y for y in raw if y['st']>st),None)
 end=next_decl
 if nxt:
  for k in range(nxt['st']-1,x['st'],-1):
   if lines[k].lstrip().startswith('/--'): end=k; break
  # no documentation still leaves source up to next declaration marker
 x.update(doc=doc, enddoc=end)
blocks=[]
for x in ordered:
 text=''.join(lines[x['doc']:x['enddoc']]); blocks.append({'name':x['name'],'start_line':x['doc']+1,'decl_line':x['st']+1,'end_line_exclusive':x['enddoc']+1,'sha256':hashlib.sha256(text.encode()).hexdigest(),'text':text})
header=''.join(lines[:20]); content=header+''.join(b['text'] for b in blocks)+f'\nend AspisR1SelectedMaskProbe\n\n#print axioms AspisR1SelectedMaskProbe.{target}\n'
out=Path(f'/tmp/TerminalV4FocusedClosure-{version}.lean');out.write_text(content)
manifest={'source_path':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'source_bytes':src.stat().st_size,'target':'AspisR1SelectedMaskProbe.'+target,'source_target_occurrences':[i+1 for i,l in enumerate(lines) if target in l][:10],'closure_count':len(blocks),'closure_raw_declaration_bytes':sum(len(b['text'].encode()) for b in blocks),'chunk_path':str(out),'chunk_sha256':hashlib.sha256(content.encode()).hexdigest(),'chunk_bytes':len(content.encode()),'declaration_blocks':[{'name':b['name'],'start_line':b['start_line'],'decl_line':b['decl_line'],'end_line_exclusive':b['end_line_exclusive'],'sha256':b['sha256']} for b in blocks],'body_reordering':'none; source order','body_edits':'none; declaration spans copied from the generated Funs source','closure_method':'textual references to declarations among top-level def/impl/instance/etc blocks, rooted at target; includes only generated declaration bodies in transitive identifier closure'}
Path(f'/tmp/TerminalV4FocusedClosure-{version}.json').write_text(json.dumps(manifest,indent=2)+'\n'); print(json.dumps({k:manifest[k] for k in ('source_sha256','chunk_sha256','chunk_bytes','closure_count','closure_raw_declaration_bytes')},indent=2))
