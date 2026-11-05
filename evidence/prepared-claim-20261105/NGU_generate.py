from pathlib import Path
import json,re,hashlib,sys
E=Path(__file__).resolve().parent;G=json.loads((E/'NGU_SOURCE_GRAPH.json').read_text());D=json.loads((E/'NGU_DISCOVERY.json').read_text())
reuse=D['reuse'];rename=D['namespace_map'];admitted=set(D['admitted'])
# Canonical compact helpers: use the existing owner, never clone it.
for n in G:
 if n.startswith('LPt_LPl_'):reuse[n]='NFU_'+n[4:]
for n in ['LPt_LPn_ExpandSpatial','LPt_LPn_ExpandTrace']:reuse[n]='NFU_'+n[4:]
compact_ns=['LPt_LPl_Kit_Release','LPt_LPl_Kit_Field','LPt_LPl_A','LPt_LPl_C','LPt_LPl_G','LPt_LPl','LPt_LPn']
for n in compact_ns:rename[n]='NFU_Retarget.'+n[4:]
rename['LPt_External']='NFU_Retarget'
# Reuse the already established canonical powers producer modules.
for n in ['LPi_PowersStep','LPi_PowersPrefix','LPi_PowersValue','LPi_PowersSource','LPm_StubBounds','LPm_PowersBridge']:
 reuse[n]='NFW_'+n;rename[n]='NFW_'+n
custom={'LPq_Powers':'NGU_Powers','LPq_WeightedStep':'NGU_WeightedStep','LPq_Weighted':'NGU_Weighted','LPq_WeightedStep':'NGU_WeightedStep','XRy_ArrayRead':'NGU_ArrayRead','XRy_ArrayMap':'NGU_ArrayMap','XRo_Join_Carriers':'NGU_Carriers','XRo_Join_ResultTransport':'NGU_ResultTransport'}
reuse.update(custom);rename.update(custom)
# Index arithmetic has no dependency on powers; its old import was aggregate.
overrides={'LPq_IndexPorts':['NGU_Carriers'],'LPq_Decoder':G['LPq_Decoder']['imports']+['NGU_Powers']}
order=[];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 if n in reuse or n in admitted or n.startswith('NGU_'):return
 assert not n.startswith(('XR','FIq')),('forbidden dependency',n)
 for d in overrides.get(n,G[n]['imports']):visit(d)
 order.append(n)
for n in ['LPq_SixPoints','LPt_PreparedClaim','LPq_CarrierFacts']:visit(n)
rename.update({n:'NGU_'+n for n in order})
groups=[];group=[];lines=0
for n in order:
 size=len(G[n]['source'].splitlines())
 if group and lines+size>450:groups.append(group);group=[];lines=0
 group.append(n);lines+=size
if group:groups.append(group)
owner={n:f'NGU_Part{i:03}' for i,ns in enumerate(groups) for n in ns};owner.update(reuse)
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
files=[]
for n in order:
 r=G[n];src=r['source'];body='\n'.join(l for l in src.splitlines() if not l.startswith('import '))+'\n';text=pat.sub(lambda m:rename[m.group()],body)
 changes=['imports','qualified owner/proof names']
 if 'verifier.Phase' in text:
  text=re.sub(r'(?<![A-Za-z0-9_.])verifier.Phase','RPz7_PhaseIso.Phase',text)
  changes+=['replace legacy observer owner by canonical finish Phase owner']
 if n=='JGi_FinishFields':
  text=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1PublicPreparation.core.result.Result.map_err',text)
  changes+=['fully qualify emitted PublicPreparation map_err owner']

 if n=='LPm_PointLoop':
  text=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1CurrentPreparedClaim.core.result.Result.map_err',text)
  changes+=['qualify SAME emitted map_err owner shadowed by canonical library']
 if n=='LPq_Decoder':
  text=text.replace('bind_map,unwrap,','NGU_ResultTransport.bind_map,NGU_LPq_Decoder.unwrap,')
  changes+=['qualify SAME unwrap theorem shadowed by canonical library']

 # Zero carrier is the SAME eight zeros, independently of legacy arithmetic ports.
 if n=='LPq_PreparedTrace':
  a=text.index('  rw [NGU_Powers.claim,');b=text.index('\n',a)
  text=text[:a]+'  unfold zero FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO\n    FIo_Native.aspis_core.field.QM31.ZERO aspis_core.field.WideExact.ZERO aspis_core.field.QM31.ZERO\n  rfl'+text[b:];changes+=['new definitional proof of zero_claim against canonical claim port']
 imports=[]
 for d in overrides.get(n,r['imports']):
  d=owner.get(d,d)
  if d not in imports:imports.append(d)
 audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
 out=''.join('import '+d+'\n' for d in imports)+'import Lean\n'+text+audit
 # Grouped modules preserve each declaration's namespace and proof text.
 files.append(dict(source_module=n,source_path=r['path'],source_sha256=hashlib.sha256(src.encode()).hexdigest(),source_line_range=[1,len(src.splitlines())],target_module=owner[n],imports_before=r['imports'],imports_after=imports,before_body=body,after_body=text,changes=changes))
for i,names in enumerate(groups):
 module=f'NGU_Part{i:03}';imports=['Lean'];bodies=[]
 for r in files:
  if r['source_module'] not in names:continue
  for d in r['imports_after']:
   if d!=module and d not in imports:imports.append(d)
  bodies.append('-- Retargeted '+r['source_module']+'\n'+r['after_body'])
 out=''.join('import '+d+'\n' for d in imports)+'\n'.join(bodies)+audit
 p=E/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==out,p
 else:p.write_text(out)
pro=dict(order=order,groups=groups,module_owner=owner,namespace_map=rename,overrides=overrides,files=files)
(E/'NGU_PROVENANCE.json').write_text(json.dumps(pro,indent=1)+'\n')
print('copies',len(order),'parts',len(groups));print('\n'.join(f'NGU_Part{i:03}' for i in range(len(groups))))
