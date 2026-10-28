from pathlib import Path
import re,json,lzma,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');B=D/'client-deployed-baseline'
raw=subprocess.check_output(['nm','--defined-only',str(B)],text=True);dem=subprocess.check_output(['nm','-C','--defined-only',str(B)],text=True)
byaddr={x.split(maxsplit=2)[0]:x.split(maxsplit=2)[2] for x in dem.splitlines() if len(x.split(maxsplit=2))==3}
linked={x.split(maxsplit=2)[2]:byaddr[x.split(maxsplit=2)[0]] for x in raw.splitlines() if len(x.split(maxsplit=2))==3}
target={s:n for s,n in linked.items() if any(t in n for t in ['String::from_utf8_lossy','format::format_inner','locate_build_id','Path::_join','Mapping>::new_debug','Cache::with_global'])}
rows=[]
paths=list((D/'stdlib-ir').glob('*.ll.xz'))+list((D/'client-target/release/deps').glob('*.ll'))
for p in paths:
 text=lzma.decompress(p.read_bytes()).decode() if p.suffix=='.xz' else p.read_text();current=None
 for no,line in enumerate(text.splitlines(),1):
  if line.startswith('define '):
   m=re.search(r'@("[^"\n]+"|[-A-Za-z$._0-9]+)\(',line);current=m[1].strip('"') if m else None
  if current and not line.lstrip().startswith(';') and re.search(r'\b(call|invoke)\b',line):
   refs=re.findall(r'@("[^"\n]+"|[-A-Za-z$._0-9]+)',line)
   for s in refs:
    s=s.strip('"')
    if s in target:rows.append(dict(file=p.name,line=no,caller=current,caller_name=linked.get(current),linked_caller=current in linked,target=target[s],instruction=line.strip()))
  if line.startswith('}'):current=None
(D/'stdlib-callers.json').write_text(json.dumps(dict(targets=target,callers=rows,complete=False,reason='Direct IR xrefs; indirect dispatch callers remain separately enumerated.'),indent=2)+'\n')
for x in rows:
 if x['linked_caller']:print(x['caller_name'],'->',x['target'])
