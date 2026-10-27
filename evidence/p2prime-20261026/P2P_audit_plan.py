from pathlib import Path
import json
P=Path(__file__).resolve().parent;R=P.parents[1]
base=json.loads((R/'evidence/recount6-20261026/Rc6_audit_plan.json').read_text());by={a['module'].removeprefix('Rc6_Audit'):a for a in base}
labels=[a['module'].removeprefix('Rc6_Audit') for a in base[:29]]+['Game','Persistence','Projection','Physical','ParserPacket','Selection','Composition','Axioms']
assert len(labels)==37
custom={
'Result':['#print AspisR1.Rc6_Result.Outcome','#print AspisR1.P2P_Result.Outcome','#print AspisR1.P2P_GoodResult.Outcome'],
'Continuation':['#print AspisR1.Rc6_Caller.Outcome','#print AspisR1.P2P_Caller.Outcome','#print AspisR1.Rc5_Cont.Outcome'],
'Nonvacuity':['#print AspisR1.P2P_Acceptance.Facts','#print AspisR1.P2P_Acceptance.Nonrejecting','#check @AspisR1.P2P_NativeNonvacuity.accepted_input','#check @AspisR1.P2P_Nonvacuity.exists_clean','#check @AspisR1.Rc5_RuntimeFixture.joint_runtime'],
'Selection':['#print AspisR1.P2P_NativeSelection.pair','#check @AspisR1.P2P_NativeSelection.on_cuts','#print AspisR1.P2P_Origin.Fact','#print AspisR1.F3T_AccountCharge.mass','#check @AspisR1.P2P_Accounting.single_event'],
'Composition':['#check @AspisR1.Rc6_Top.deployed','#check @AspisR1.P2P_Top.deployed','#check @AspisR1.P2P_Release.remove','#check @AspisR1.P2P_Projection.good','#check @AspisR1.P2P_Forget.forget'],
'Axioms':[]}
for mod in sorted((R/'lean').glob('P2P_*.lean')):
 import re
 text=mod.read_text()
 for name in re.findall(r'^#print axioms (\w+)',text,re.M):
  namespace=re.search(r'^namespace (\S+)',text,re.M)[1]
  custom['Axioms'].append('#print axioms '+namespace+'.'+name)
header=(R/'lean/Rc6_AuditSdk.lean').read_text().split('#print AspisR1.S2Trust.S2TrustedSdkBorrow')[0]
extra=''.join('import P2P_'+m+'\n' for m in ['Top','Forget','NativeNonvacuity','Projection','Accounting','Nonvacuity','ByteTransport','AccountBinding','Authentication','PersistenceGap'])
plan=[]
for n,label in enumerate(labels,64):
 commands=custom.get(label,by.get(label,{}).get('commands',[]));assert commands,label
 module='P2P_Audit'+label
 (R/'lean'/(module+'.lean')).write_text(extra+header+'\n'.join(commands)+'\n')
 plan.append(dict(attempt=f'P2P_{n:03}',module=module,commands=commands))
(P/'P2P_audit_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
