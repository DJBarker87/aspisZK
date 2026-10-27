from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];lean=R/'docs/research/v8-r0-zk-20261009/lean'
root_names=['R1Z.PV_CB_CandidateAudit','R1Z.PV_CB3_CallbackBundle','R1Z.PV_CBM_CallbackBundle','R1Z.PV_Op134_ReferenceBundle','R1Z.PV_CBL_CallbackBundle','R1Z.PV_CBL_CallbackPublication','R1Z.PV_Join_AggregateCaller','PV_L2B_Manifest','R1Z.PV_Op223_AuditFinal']
resolution={}
for p in lean.rglob('*.lean'):resolution['.'.join(p.relative_to(lean).with_suffix('').parts)]=str(p.relative_to(R))
# Candidate's extraction cohort is explicit, rather than selected by a grep hit.
for p in (R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023').glob('*.lean'):resolution['R1Z.'+p.stem]=str(p.relative_to(R))
resolution['ProverRwSampler.Funs']='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwSampler/Funs.lean'
resolution['ProverRwSampler.Types']='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwSampler/Types.lean'
# Shared authority overrides the convenience repository map.
for row in json.loads((R/'evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_text())['selected']:
 if row.get('resolution'):resolution[row['module'].replace('/','.')]=row['resolution']['path']
def clean(t):
 t=re.sub(r'/\-.*?\-/','',t,flags=re.S);return re.sub(r'--[^\n]*','',t)
def imports(t):return [x for line in re.findall(r'^import\s+([^\n]+)',clean(t),re.M) for x in line.split()]
# Inline command-only audits; they need no .olean and contain no declarations.
audit_imports=set();commands=set();audit_sources={}
def expand(n):
 p=R/resolution[n];t=p.read_text();audit_sources[n]=str(p.relative_to(R))
 if re.search(r'^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure|inductive|namespace|instance)\b',clean(t),re.M):
  audit_imports.add(n)
  ns=re.search(r'^namespace\s+(\S+)',t,re.M)
  if ns:
   for name in re.findall(r'^(?:protected\s+)?(?:theorem|lemma)\s+(\S+)',clean(t),re.M):commands.add(ns[1]+'.'+name)
 else:
  for m in imports(t):expand(m)
 for name in re.findall(r'^#print axioms\s+(\S+)',t,re.M):
  if '.' in name and (name.startswith(('R1Z.','PV_L2B_'))):commands.add(name)
  elif ns if 'ns' in locals() else False:commands.add(ns[1]+'.'+name)
for n in root_names:expand(n)
# Candidate publication audit has explicit fully qualified top and supporting targets.
for p in (lean/'R1Z').glob('PV_CB_*Audit*.lean'):
 for name in re.findall(r'^#print axioms\s+(\S+)',p.read_text(),re.M):
  if name.startswith('R1Z.PV_CB_'):commands.add(name)
# Pull each command's defining publication module into the audit (longest prefix).
for name in sorted(commands):
 matches=[n for n in resolution if name.startswith(n+'.')]
 if matches:audit_imports.add(max(matches,key=len))
text=''.join('import '+n+'\n' for n in sorted(audit_imports))+'\n-- Combined integration publication audit; no new theorem or source refinement.\n'+''.join('#print axioms '+n+'\n' for n in sorted(commands))
(E/'PV_Integ2_CombinedAudit.lean').write_text(text)
closure={};unresolved=set()
def walk(n):
 if n in closure:return
 if n not in resolution:
  if not n.startswith(('Mathlib','Aeneas','Lean','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','Cli','LeanSearchClient')):unresolved.add(n)
  return
 p=R/resolution[n]
 if not p.exists():unresolved.add(n);return
 t=p.read_text();closure[n]=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=imports(t))
 for m in closure[n]['imports']:walk(m)
for n in sorted(audit_imports):walk(n)
(E/'formal-plan.json').write_text(json.dumps(dict(roots=root_names,audit_imports=sorted(audit_imports),audit_targets=sorted(commands),closure=closure,unresolved=sorted(unresolved),audit_sources=audit_sources),indent=2)+'\n')
print('imports',len(audit_imports),'targets',len(commands),'closure',len(closure),'unresolved',sorted(unresolved))
