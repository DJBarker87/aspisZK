from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
data=json.loads((E/'TAu_closure-working.json').read_text()); mods=data['modules']
def clean(text):
 return re.sub(r'/\-.*?\-/','',text,flags=re.S)
def names(text):
 stack=[];out=[]
 for line in clean(text).splitlines():
  line=line.split('--')[0].strip()
  if m:=re.match(r'namespace\s+(\S+)',line):stack.append(m[1]);continue
  if re.match(r'(?:noncomputable\s+)?section\b',line):stack.append('');continue
  if re.match(r'end(?:\s|$)',line):
   if stack:stack.pop()
   continue
  if m:=re.match(r'(?:(?:noncomputable|protected|unsafe|partial|private|public)\s+)*(axiom|opaque|theorem|lemma|def|abbrev|structure|inductive|class)\s+([^\s(:{]+)',line):
   if 'private ' in line[:m.start(2)]:continue
   n='.'.join(x for x in stack+[m[2]] if x)
   if n.startswith('_root_.'):n=n[7:]
   out.append([n,m[1]])
 return out
quote=lambda n:'.'.join('«'+s+'»' for s in n.split('.'))
axioms={};samples=[];coverage=[]
for m,r in mods.items():
 ns=names(r.get('source_text',''))
 r['source_declarations']=ns
 for n,k in r['raw_declarations']+ns:
  if k=='axiom':axioms[n]=m
 raw=[(n,k) for n,k in r['raw_declarations'] if not n.startswith('_private')]
 opts=ns or raw
 ranked=sorted(opts,key=lambda a:(a[1] not in ['theorem','lemma'],len(a[0])))
 if ranked:
  n,k=ranked[0];samples.append((m,n));coverage.append(dict(module=m,name=n,basis='source lexical' if ns else 'raw census'))
 else:coverage.append(dict(module=m,name=None,basis='no available named declaration'))
(E/'TAu_coverage-plan.json').write_text(json.dumps(dict(modules=coverage,axioms=axioms,missing=data['missing']),indent=2)+'\n')
# First two attempts inspect actual headlines and exact trust definitions.
special=[['#check @AspisR1.FGl_Headline.deployed','#check @AspisR1.Rc6_Top.deployed','#print axioms AspisR1.FGl_Headline.deployed','#print axioms AspisR1.Rc6_Top.deployed','#check @AspisR1.FGl_Nonvacuity.composed','#print axioms AspisR1.FGl_Nonvacuity.composed'],[]]
for n in ['S2Trust.S2TrustedSdkBorrow','S2W_TrustedStd.TrustedStd','S2W_TrustedStd.specification','S2W_D189Wrappers.Allocator','S2W_D189Consolidation.RuntimeEntrypointAdmission','AdapterRw.RuntimeEntrypointAdmission','S2W_DigestExtraction.AeneasExtraction','S2W_ExtractionBoundary.P1','S2W_ExtractionBoundary.RuntimeSyscall','S2Z.Oracle.P1Realization','S2Z.Oracle.RuntimeSyscall','S2X.CheckpointVersionBinding','CPR_DataPersistence.TwoTransactionLaw','CPH_Game.DeployedPairExecution','CPG_Projection.ordinary','CPG_Projection.adjacent','CPG_RuntimeTrace.Executes','FGl_PreparedAt.Owners','FGl_FinishLeaves.Holds']:
 special[1].extend(['#print AspisR1.'+n,'#print axioms AspisR1.'+n])
# Ax. candidates include historical native-decide names; absence is recorded, never assumed present.
commands=['#print axioms '+quote(n) for n in sorted(axioms)]
commands+=['#print axioms '+quote(n) for m,n in samples]
chunks=[commands[i::28] for i in range(28)]
base=json.loads((E/'TAu_base.json').read_text());rev=__import__('subprocess').check_output(['git','rev-parse','HEAD'],text=True).strip()
for i,cmds in enumerate(special+chunks,1):
 mod=f'TAu_Audit{i:03d}';src=E/(mod+'.lean')
 src.write_text('import FGl_Headline\nimport Rc6_Top\nimport FGl_Nonvacuity\n'+ '\n'.join(cmds)+'\n')
 cfg=dict(kind='lean',env=base['env'],timeout=180,command=base['command'][:6]+[mod+'.lean'],sources=[mod+'.lean'],attempt=f'TAu_{i:03d}',source_revision=rev,source_tree_dirty=True,deps_fingerprint=dict(scope='TAu read-only axioms/trust queries over selected coherent SInt2 closure'),expected_time='Kernel print/check queries only; no proof or dependency compilation')
 (E/(f'TAu_{i:03d}.json')).write_text(json.dumps(cfg,indent=2)+'\n')
# Compact provenance; source bytes and huge raw declaration census are reused, not duplicated.
compact=[]
for r in mods.values():compact.append({k:v for k,v in r.items() if k not in ['source_text','raw_declarations','source_declarations']})
(E/'TAu_closure.json').write_text(json.dumps(dict(raw_census_sha256=data['raw_census_sha256'],modules=compact,missing=data['missing']),indent=2)+'\n')
print('modules',len(mods),'query modules',len(samples),'axiom candidates',len(axioms),'commands',len(commands))
