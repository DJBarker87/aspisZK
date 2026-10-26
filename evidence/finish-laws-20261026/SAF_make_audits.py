from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];P=R/'evidence/finish-laws-20261026'
settings='''set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
'''
plan=[
('TopCompare',['Rc3_Top','SAF_Deployed','SAF_CompatibleTop'],'#check @AspisR1.Rc3_Top.deployed\n#check @AspisR1.SAF_Deployed.deployed\n#check @AspisR1.SAF_CompatibleTop.deployed'),
('Results',['SAF_Deployed'],'#print AspisR1.Rc3_Result.Outcome\n#print AspisR1.SAF_C_SAF_FinalResult.Outcome'),
('Callers',['SAF_Deployed'],'#print AspisR1.SAP_LiteralCaller.Outcome\n#print AspisR1.SAF_C_SAF_PreparedCaller.Outcome'),
('Continuations',['SAF_Deployed'],'#print AspisR1.SAP_LiteralCont.Outcome\n#print AspisR1.SAF_C_SAF_PreparedCont.Outcome'),
('LiteralOutcomes',['SAF_Deployed'],'#print AspisR1.SAP_LiteralOutcome.Outcome\n#print AspisR1.SAF_C_SAF_PreparedOutcome.Outcome'),
('FinishBeforeAfter',['SAF_Deployed','SAF_ForgetFinish'],'#print AspisR1.SAP_FinishSaved.Outcome\n#print AspisR1.SAF_C_SAF_FinishPrepared.Outcome\n#check @AspisR1.SAF_ForgetFinish.forget'),
('RoundValues',['RowFinish_Control'],'#print AspisR1.RowFinish_Control.RoundValues'),
('PairingFields',['SAF_ReducedLaws'],'#print AspisR1.Port4D_Pairing.RoundLaws\n#print AspisR1.Port4D_Pairing.PairingLaws\n#print AspisR1.SAF_ReducedLaws.Arithmetic'),
('ReturnWitnesses',['SAF_Returns','SAF_RoundUnique'],'#check @AspisR1.SAF_Returns.finish\n#check @AspisR1.SAF_RoundUnique.unique'),
('SavedIdentities',['SAF_PreparedPairing'],'#check @AspisR1.SAF_SavedIdentities.fields\n#check @AspisR1.SAF_PreparedPairing.identities'),
('CanonicalRemoval',['SAF_C_Cons_FinishProof'],'#check @AspisR1.SAF_AcceptedValue.value\n#check @AspisR1.SAF_C_Cons_FinishProof.strengthen'),
('LibraryTrust',['SAF_Deployed'],'#print AspisR1.S2Trust.S2TrustedSdkBorrow'),
('Extraction',['SAF_Deployed'],'#print AspisR1.S2W_DigestExtraction.AeneasExtraction\n#print AspisR1.S2W_ExtractionBoundary.RuntimeSyscall'),
('EntryTrust',['SAF_Deployed'],'#print AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission\n#print AspisR1.S2W_TrustedStd.TrustedStd'),
('QueryFields',['SAF_Deployed'],'#print AspisR1.Port5Q1_QueryPorts.SessionAPrimitives\n#print AspisR1.Port5Q1_GeometryCanonical.SessionAPrimitives\n#print AspisR1.Port5Q1_Domain.SessionADomain'),
('SemanticRows',['SAF_Deployed'],'#print AspisR1.R3SemanticRemainingJoins.EquationEndpoint\n#print AspisR1.R3SemanticEquationCore.Equations'),
('MatchingRow',['SAF_Deployed'],'#print AspisR1.MatchingSupport.match0'),
('Configuration',['SAF_Deployed'],'#print AspisR1.DrvC_Installation.Configuration\n#print AspisR1.Rc3_Install.configuration\n#print AspisR1.Port3_FinishStage.release'),
('Nonvacuity',['SAF_Deployed'],'#print AspisR1.Rc3_Nonvacuity.Facts\n#check @AspisR1.Rc3_Nonvacuity.derive\n#check @AspisR1.SAF_Returns.finish'),
('Compatibility',['SAF_CompatibleTop'],'#check @AspisR1.SAF_ForgetResult.forget\n#check @AspisR1.SAF_CompatibleTop.deployed'),
('RawBoundary',['SAF_Deployed'],'#print AspisR1.Port1_CanonicalJoin.AcceptedVerifierJoin\n#print AspisR1.OraclePortRuntimeBindingC7.StoredCarrierBinding')
]
out=[]
plan = plan[:-1]
for n,(name,imports,body) in enumerate(plan,81):
 m='SAF_Audit'+name
 (R/'lean'/f'{m}.lean').write_text(''.join('import '+i+'\n' for i in imports)+settings+body+'\n')
 out.append(dict(attempt=f'SAF_{n:03}',module=m,kind=name,status='planned'))
(P/'SAF_audit_plan.json').write_text(json.dumps(out,indent=2)+'\n')
