"""Emit focused type/field inventories for the actual composed root."""
from pathlib import Path
import ast,json
P=Path(__file__).resolve().parent; R=P.parents[1]
tree=ast.parse((R/'evidence/recount4-20261026/Rc4_make_audits.py').read_text())
specs=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='specs' for t in n.targets))
replace={
'BeforeAfter':['#check @AspisR1.Rc4_Top.deployed','#check @AspisR1.Rc5_Top.deployed','#check @AspisR1.CPH_Top.deployed','#check @AspisR1.SAF_Deployed.deployed'],
'Statement':['#print AspisR1.Rc4_Statement.Conclusion','#print AspisR1.Rc5_Result.Outcome'],
'Result':['#print AspisR1.Rc5_Result.Outcome','#check @AspisR1.Rc5_ResultForget.forget','#print AspisR1.SAF_C_SAF_FinalResult.Outcome'],
'Continuation':['#print AspisR1.Rc5_Caller.Outcome','#print AspisR1.Rc5_Cont.Outcome'],
'Literal':['#print AspisR1.Rc5_Literal.Outcome','#check @AspisR1.Rc5_LiteralForget.forget'],
'Finish':['#print AspisR1.SAF_C_SAF_FinishPrepared.Outcome','#print AspisR1.RowFinish_Control.RoundValues'],
'FinishLaws':['#print AspisR1.SAF_ReducedLaws.Arithmetic','#print AspisR1.Port4D_Pairing.RoundLaws','#print AspisR1.R3SemanticRemainingJoins.EquationEndpoint','#print AspisR1.MatchingSupport.match0'],
'Nonvacuity':['#print AspisR1.Rc5_Nonvacuity.Facts','#check @AspisR1.Rc5_Nonrejecting.accepted_input','#check @AspisR1.Rc5_RuntimeFixture.joint_runtime','#check @AspisR1.Rc5_DictionaryNonvacuity.contracts','#print AspisR1.CPP_Acceptance.Facts'],
'Bank':['#print AspisR1.Rc2_Events.Facts','#print AspisR1.Rc2_Protection.Facts','#print AspisR1.CPH_Protection.Facts'],
'Configuration':['#print AspisR1.Rc5_Install.configuration','#print AspisR1.Rc5_Install.seed','#check @AspisR1.Rc5_Install.rc4','#check @AspisR1.Rc5_Install.saf','#check @AspisR1.Rc5_Install.cph'],
'RawJoin':['#print AspisR1.F3T_CanonicalJoin.AcceptedVerifierJoin','#print AspisR1.F3T_Runtime.StoredCarrierBinding','#print AspisR1.F3T_ByteCarrier.input','#print AspisR1.F3T_ByteCarrier.semantic'],
'Axioms':[f'#print axioms AspisR1.{name}' for name in ['Rc5_Top.deployed','Rc5_Close.from_saf','Rc5_Source.source','Rc5_ResultForget.forget','Rc5_Caller.strengthen','Rc5_CallerForget.forget','Rc5_Cont.strengthen','Rc5_ContForget.forget','Rc5_Literal.strengthen','Rc5_LiteralForget.forget','Rc5_Install.rc4','Rc5_Install.saf','Rc5_Install.cph','Rc5_Install.key','Rc5_RuntimeFixture.joint_runtime','Rc5_Nonrejecting.accepted_input','Rc5_DictionaryNonvacuity.contracts','Rc5_DictionaryNonvacuity.model_surjective','Rc5_DictionaryNonvacuity.data_surjective']]
}
specs=[(name,replace.get(name,commands)) for name,commands in specs]
specs += [
('Game',['#print AspisR1.CPH_Game.DeployedPairExecution','#check @AspisR1.CPH_Game.recordedInstance','#print AspisR1.CPG_RuntimeTrace.Executes']),
('Persistence',['#print AspisR1.CPR_DataPersistence.TwoTransactionLaw','#print AspisR1.CPR_DataPersistence.Image','#print AspisR1.CPR_DataPersistence.visible','#print AspisR1.CPG_Projection.ordinary']),
('Projection',['#print AspisR1.CPG_Projection.Observations','#print AspisR1.CPG_Projection.adjacent','#print AspisR1.GExq_AccountExperiment.FirstInputs','#print AspisR1.GExq_AccountExperiment.SecondInputs','#print AspisR1.GExq_AccountExperiment.program']),
('Physical',['#print AspisR1.CPH_Trace.Facts','#print AspisR1.CPH_Recorder.Facts','#print AspisR1.CPH_Protection.Facts','#check @AspisR1.CPH_Protection.derive']),
('Composition',['#check @AspisR1.Rc5_Source.source','#check @AspisR1.Rc5_Close.from_saf','#check @AspisR1.Rc5_ResultForget.forget','#check @AspisR1.SAF_ForgetFinish.forget'])]
# The first two audit probes exposed missing explicit Rc4 imports (023/024).
# Split their required evidence into the final Composition audit; retain failures.
carry=replace['BeforeAfter']+replace['Statement']
specs=[(n,c+carry if n=='Composition' else c) for n,c in specs if n not in {'BeforeAfter','Statement'}]
assert len(specs)==36
imports='''import Rc4_Top
import Rc5_Top
import Rc5_ResultForget
import Rc5_RuntimeFixture
import Rc5_Nonrejecting
import Rc5_DictionaryNonvacuity
import Rc4_Nonvacuity
import Rc4_ResultForget
import CPH_Top
import SAF_Deployed
import SAQ_CompleteTop
import TxS_Top
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
'''
plan=[]
for n,(name,commands) in enumerate(specs,25):
 m='Rc5_Audit'+name
 (R/'lean'/(m+'.lean')).write_text(imports+'\n'.join(commands)+'\n')
 plan.append(dict(attempt=f'Rc5_{n:03}',module=m,commands=commands))
(P/'Rc5_audit_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
