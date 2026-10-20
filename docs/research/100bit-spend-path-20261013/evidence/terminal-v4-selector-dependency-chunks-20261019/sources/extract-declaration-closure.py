import re, pathlib, json,hashlib
p=pathlib.Path('/tmp/terminal-v4-model-sources-20261019/AspisR1SelectedMaskProbe/Funs.lean')
s=p.read_text(); lines=s.splitlines(keepends=True)
key=r'(?:def|abbrev|opaque|theorem|instance|impl_def|inductive|structure|class|axiom|constant)'
starts=[]
for i,line in enumerate(lines):
 if re.match(r'^'+key+r'\b',line): starts.append(i)
 elif line.startswith('@['):
  # Attribute can be on the same line or occupy several lines; generated declaration follows within 8 lines.
  for k in range(i,min(i+9,len(lines))):
   if re.match(r'^'+key+r'\b',lines[k]) or re.search(r'\]\s*'+key+r'\b',lines[k]):
    starts.append(i); break
starts=sorted(set(starts))
items=[]
for j,st in enumerate(starts):
 en=starts[j+1] if j+1<len(starts) else len(lines)
 head=''.join(lines[st:min(st+10,en)])
 m=re.search(r'\b'+key+r'\s+([^\s(:]+)',head,re.M)
 if not m: continue
 name=m.group(1)
 items.append({'name':name,'start':st,'end':en,'body':''.join(lines[st:en])})
by={x['name']:x for x in items}
names=sorted(by,key=len,reverse=True)
refs={x['name']:set(n for n in names if n!=x['name'] and re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w.])',x['body'])) for x in items}
target='pool_v1.pair_forest_copy_terminal.selector_mask_sum_16'
seen=set();todo=[target]
while todo:
 n=todo.pop()
 if n in seen: continue
 seen.add(n); todo.extend(x for x in refs.get(n,()) if x not in seen)
selected=[x for x in items if x['name'] in seen]
print('lines',len(lines),'decls',len(items),'selected',len(selected),'source bytes',len(s.encode()),'selected bytes',sum(len(x['body'].encode()) for x in selected))
print('target exists',target in by)
for x in selected:print(x['name'],x['start']+1,x['end'],len(x['body'].encode()),'deps',len(refs[x['name']]))
pathlib.Path('/tmp/terminal-v4-funs-closure-selection.json').write_text(json.dumps({'source':str(p),'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'target':target,'selected':[{'name':x['name'],'start_line':x['start']+1,'end_line_exclusive':x['end']+1,'bytes':len(x['body'].encode())} for x in selected]},indent=2)+'\n')
