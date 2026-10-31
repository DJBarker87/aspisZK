from pathlib import Path
import re,subprocess,json,hashlib
B=Path(__file__).resolve().parent
T=Path('/home/dombarker/.kani/kani-0.67.0')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tools={n:dict(path=str(T/'bin'/n),sha256=sha(T/'bin'/n)) for n in ['kani-compiler','kani-driver','cbmc','goto-instrument']}
results=[]
for a in ['NEF_K021','NEF_K023','NEF_K027','NEF_K033']:
 cfg=json.loads((B/(a+'.json')).read_text());name=cfg['module'].split('::')[-1]
 archived=list((B/a/'NEF_artifacts').glob('*.out'))
 current=[p for p in (B/'NEF_target').rglob('*.out') if name in p.name and not p.name.endswith('.symtab.out')]
 files=archived or current
 for p in files:
  r=subprocess.run([str(T/'bin/goto-instrument'),'--show-goto-functions',str(p)],capture_output=True,text=True);assert r.returncode==0,r.stderr
  blocks=re.split(r'\n(?=[^\n]* /\* [^\n]* \*/\n)',r.stdout);functions={};pretty={}
  for block in blocks:
   m=re.match(r'([^\n]+) /\* ([^\n]+) \*/\n',block)
   if not m:continue
   functions[m[2]]=block;pretty[m[2]]=m[1]
  roots=[s for s,n in pretty.items() if n==cfg['module']];assert len(roots)==1,(a,roots)
  reached=set();missing=set()
  def visit(s):
   if s in reached:return
   if s not in functions:missing.add(s);return
   reached.add(s)
   for callee in re.findall(r'\bCALL (?:[^\n]*? := )?([^\s(]+)\(',functions[s]):visit(callee)
  visit(roots[0]);text='\n'.join(functions[s] for s in reached)
  fn_tests=[l for l in text.splitlines() if any(w in l for w in ['Option::<fn','FnPtr','dereferenced function pointer must','no candidates for dereferenced function pointer'])]
  indirect=[l for l in text.splitlines() if 'CALL ' in l and ('CALL *' in l or ' := *' in l)]
  copies=[pretty[s] for s in reached if any(k in pretty[s] for k in ['copy_from_slice','copy_nonoverlapping','clone_from_slice','to_vec','realloc'])]
  static_assigns=[l for l in text.splitlines() if 'ASSIGN ' in l and ('NEF_' in l or 'NBZ_' in l) and '::1::' not in l and '::$tmp::' not in l]
  # Collection is diagnostic: source-level modifies and graph review remain necessary.
  results.append(dict(attempt=a,goto_path=str(p),goto_sha256=sha(p),artifact_from_attempt=bool(archived),source_configuration='archived exact' if archived else 'current diagnostic; never retroactively attributed to earlier configuration',reachable_count=len(reached),missing_callees=sorted(missing),function_pointer_tests=fn_tests,indirect_calls=indirect,copy_related_functions=copies,possible_static_assigns=static_assigns,reachable_functions=sorted(pretty[s] for s in reached)))
print(json.dumps(dict(tools=tools,results=results),indent=2))
