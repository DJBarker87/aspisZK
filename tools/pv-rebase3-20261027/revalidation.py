"""Read-only import inventory: shared names use h' rebuild resolutions."""
import pathlib,json,subprocess,re,collections
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-rebase3-20261027';base='237e135561';build='37794d7bff'
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True).splitlines()
changed=set(git('diff','--name-only',base,build,'--','*.lean'));old=git('ls-tree','-r','--name-only',base)
proofs=[p for p in old if re.search(r'/(ProverRw[^/]*|PV_[^/]*)\.lean$',p) and '/lean/' in p and '/evidence/' not in p]
resolution={};authority={}
# Job-owned modules absent from the historical shared inventory.
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('*.lean'):
 n='R1Z.'+p.stem;resolution[n]=str(p.relative_to(R));authority[n]='canonical R1Z repository source'
for p in (R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023').glob('ProverRwFull*.lean'):
 n='R1Z.'+p.stem;resolution[n]=str(p.relative_to(R));authority[n]='candidate full-extraction cohort (imports name R1Z)'
r=json.loads((R/'evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_text())
for row in r['selected']:
 if row.get('resolution'):
  n=row['module'].replace('/','.');resolution[n]=row['resolution']['path'];authority[n]="h' EJR selected resolution"
imports={};missing=set()
def import_names(text):
 # Retain line breaks, strip nested Lean block and line comments.
 tokens=re.split(r'(/-|-/|--|\n)',text);depth=0;line_comment=False;out=[]
 for t in tokens:
  if t=='\n':out.append(t);line_comment=False;continue
  if line_comment:continue
  if t=='/-':depth+=1;continue
  if t=='-/' and depth:depth-=1;continue
  if depth:continue
  if t=='--':line_comment=True;continue
  out.append(t)
 return [name for line in re.findall(r'^import[ \t]+([^\n]+)', ''.join(out),re.M) for name in line.split() if re.fullmatch(r'[A-Za-z_][\w.]*',name)]
def deps(p):
 if p not in imports:
  f=R/p
  if not f.is_file():missing.add(p);imports[p]=[]
  else:imports[p]=import_names(f.read_text())
 return imports[p]
rows=[]
for p in proofs:
 seen=set();todo=[p];hits=[];unresolved=set()
 while todo:
  f=todo.pop()
  if f in seen:continue
  seen.add(f)
  if f in changed:hits.append(f)
  for n in deps(f):
   if n in resolution:todo.append(resolution[n])
   elif not n.startswith(('Mathlib','Aeneas','Lean','Std','Batteries','Qq','ImportGraph','Plausible','ProofWidgets','Cli')):unresolved.add(n)
 rows.append(dict(proof=p,changed_import_sources=sorted(hits),unresolved_repository_imports=sorted(unresolved)))
result=dict(method="Shared names resolved through h' EJR selected record; own R1Z canonical modules and explicit full-extraction cohort. No shared source/object write; no final closure replay claimed.",base=base,merged_build_source=build,active_proofs=len(proofs),rows=rows,missing_resolution_paths=sorted(missing),shared_rebuild2_note='No shared object is recompiled or adopted by this task; unresolved names remain for the final cohort/closure review, including rebuild2 resolutions.')
(E/'import-revalidation.json').write_text(json.dumps(result,indent=2)+'\n')
print('active candidate modules',len(rows),'changed import closures',sum(bool(x['changed_import_sources']) for x in rows),'unresolved closures',sum(bool(x['unresolved_repository_imports']) for x in rows))
