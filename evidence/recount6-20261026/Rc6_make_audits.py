"""Fresh full inventories plus atomic-field probes, within the owner's 100 attempts."""
from pathlib import Path
import json
P=Path(__file__).resolve().parent;R=P.parents[1];L=R/'lean'
old=json.loads((R/'evidence/recount5-20261026/Rc5_audit_plan.json').read_text())
imports=(L/'Rc5_AuditComposition.lean').read_text().split('#check')[0]
imports='''import Rc6_Top
import Rc6_Statements
import Rc6_Forget
import Rc6_Equivalent
import Rc6_Nonvacuity
import P6C_CarrierGap
import P6C_Nonvacuity
'''+imports
spec=[]
for a in old:
 name=a['module'].removeprefix('Rc5_Audit');cmds=a['commands']
 if name=='Composition':cmds=cmds+['#check @AspisR1.Rc6_Top.deployed','#check @AspisR1.Rc6_Statements.reverse','#check @AspisR1.Rc6_Equivalent.same_domain']
 if name=='Result':cmds=cmds+['#print AspisR1.Rc6_Result.Outcome','#check @AspisR1.Rc6_Result.strengthen','#check @AspisR1.Rc6_Forget.forget']
 if name=='Continuation':cmds=cmds+['#print AspisR1.Rc6_Caller.Outcome','#check @AspisR1.Rc6_Caller.from_cut']
 if name=='Axioms':cmds=cmds+['#print axioms AspisR1.'+x for x in ['Rc6_Top.deployed','Rc6_Statements.reverse','Rc6_Result.strengthen','Rc6_Caller.from_cut','Rc6_Forget.forget','Rc6_Equivalent.same_domain','Rc6_Nonvacuity.accepted_input','Rc6_Install.parser_base','Rc6_Install.p6_base','Rc6_Install.reconstruct']]
 spec.append((name,cmds))
spec.extend([
 ('ParserPacket',['#print AspisR1.PFin_Packet.Facts','#check @AspisR1.PFin_Packet.from_cut']),
 ('ParserEntry',['#print AspisR1.S2W_ChildJoins.FirstEntryVerifierConeJoin','#print AspisR1.PFin_Attach.from_cut']),
 ('ParserGates',['#print AspisR1.PFin_Gates.decoded','#print AspisR1.Port5Q1_QueryPorts.SessionAPrepare']),
 ('P6Discharge',['#print AspisR1.MultiproofConeP6Frozen2Stage.P6Boundary','#check @AspisR1.P6C_Extension.boundary']),
 ('P6SameCuts',['#print AspisR1.P6C_OnCuts.SafeBatches','#check @AspisR1.P6C_OnCuts.same_cuts']),
 ('P6Full',['#print AspisR1.P6C_FullBoundary.Facts','#check @AspisR1.P6C_FullBoundary.same_cuts']),
 ('P6Accepted',['#check @AspisR1.P6C_Accepted.issued_calls_ok','#check @AspisR1.P6C_CarrierGap.independent']),
 ('Compatibility',['#check @AspisR1.Rc6_Install.parser_base','#check @AspisR1.Rc6_Install.p6_base','#check @AspisR1.Rc6_Install.reconstruct']),
 ('Rc6Nonvacuity',['#check @AspisR1.Rc6_Nonvacuity.accepted_input','#check @AspisR1.Rc6_Equivalent.same_domain']),
 ('Rc6Reverse',['#check @AspisR1.Rc6_Statements.reverse','#check @AspisR1.Rc6_Forget.forget']),
 ('Rc6TopProof',['#print AspisR1.Rc6_Top.deployed']),
 ('Rc6ResultProof',['#print AspisR1.Rc6_Result.strengthen']),
])
# Field probes come from the exact predecessor catalog, not guessed names.
cat=json.loads((R/'evidence/recount5-20261026/Rc5_field_catalog.json').read_text())
fields=[]
for key in sorted(cat):
 for field in cat[key]['field_names']:
  if field not in fields:fields.append(field)
needed=92-len(spec)
for j,field in enumerate(fields[:needed],1):spec.append((f'Atomic{j:02}',[f'#check @{field}']))
assert len(spec)==92
plan=[]
for n,(name,commands) in enumerate(spec,9):
 m='Rc6_Audit'+name
 (L/(m+'.lean')).write_text(imports+'\n'.join(commands)+'\n')
 plan.append(dict(attempt=f'Rc6_{n:03}',module=m,commands=commands))
(P/'Rc6_audit_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
