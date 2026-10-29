from pathlib import Path
import json,hashlib,re
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029');O=H/'resume-ae1'
y=json.loads((H/'inventory-73309/effect-interface.json').read_text())
rows=[]
for r in y['opaque_functions']:
 if r['effect_class']:continue
 original=r['definition']['file']['Local'];p=Path(original)
 if original.startswith('/cargo/'):p=Path('/home/dombarker/.cargo')/original.removeprefix('/cargo/')
 if original.startswith('/rustc/library/'):p=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')/original.removeprefix('/rustc/library/')
 s=p.read_text();ls=s.splitlines();start=r['definition']['beg']['line']-1;end=r['definition']['end']['line']
 indent=len(ls[start])-len(ls[start].lstrip());stop=end
 if not ls[start].rstrip().endswith(';'):
  for j in range(end,min(len(ls),end+1500)):
   if ls[j].startswith(' '*indent+'}') and (len(ls[j])==indent+1 or ls[j][indent+1:] in [';',',']):stop=j+1;break
 rows.append(dict(id=r['llbc_fun_id'],name='::'.join(t['Ident'][0] for t in r['rust_name_structured'] if 'Ident' in t),original_path=original,resolved_path=str(p),source_sha256=hashlib.sha256(s.encode()).hexdigest(),start_line=start+1,end_line=stop,definition_text='\n'.join(ls[start:stop]),call_sites=r['source_call_sites']))
(O/'source-definitions-62.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows))
