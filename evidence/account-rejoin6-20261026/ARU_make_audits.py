from pathlib import Path
import json
p=Path(__file__).resolve().parent;r=p.parents[1]
plan=[
('LocalOracle',['ARU_Support','ARQ_WorldSupport'],['#print AspisR1.S2W_ExtractionBoundary.P1','#print AspisR1.S2W_ExtractionBoundary.RuntimeSyscall','#print AspisR1.ARQ_WorldSupport.NativeAt','#print AspisR1.ARU_Support.At']),
('InstalledSource',['ARU_FullSourceAlternative','ARQ_SourceAlternative'],['#check @AspisR1.ARQ_SourceAlternative.accepted','#check @AspisR1.ARU_FullSourceAlternative.accepted','#print axioms AspisR1.ARU_FullSourceAlternative.accepted']),
('AccountCuts',['ARU_CutsOrigin','ARU_R1'],['#check @AspisR1.ARU_CutsOrigin.selected','#check @AspisR1.ARU_R1.selected','#print axioms AspisR1.ARU_R1.selected']),
('CheckpointBank',['ARQ_BankCut','ARU_ByteMatch'],['#check @AspisR1.ARQ_BankCut.checkpoint','#check @AspisR1.ARU_ByteMatch.digest_matches','#print axioms AspisR1.ARU_ByteMatch.digest_matches']),
('Recovery',['ARU_OriginalRecovery','ARQ_PerCoin'],['#check @AspisR1.ARQ_PerCoin.extract','#check @AspisR1.ARU_OriginalRecovery.extract','#print axioms AspisR1.ARU_OriginalRecovery.extract']),
('OriginalFactory',['ARU_OriginalFactory','ARU_ObstructionResolved'],['#check @AspisR1.ARU_OriginalFactory.original','#check @AspisR1.ARU_ObstructionResolved.installed','#print axioms AspisR1.ARU_ObstructionResolved.installed']),
('CoverageQuantifiers',['ARU_CoverageQuantifiers'],['#print AspisR1.ARU_CoverageQuantifiers.OriginalCoverage','#print AspisR1.ARU_AllWorld.Supported','#check @AspisR1.ARU_CoverageQuantifiers.exact_iff','#print axioms AspisR1.ARU_CoverageQuantifiers.exact_iff']),
('Carrier',['ARU_Carrier','ART_Carrier'],['#check @AspisR1.ARU_Carrier.exact','#check @AspisR1.ART_Carrier.projection','#check @AspisR1.ART_Carrier.checkpoint','#print axioms AspisR1.ARU_Carrier.exact']),
('FullWork',['ARU_Charges'],['#print AspisR1.ART_AdversaryWork.work','#print AspisR1.ART_AdversaryWork.Bound','#check @AspisR1.ARU_Charges.charged','#print axioms AspisR1.ARU_Charges.charged']),
('CollisionCharge',['ARU_Charge','ART_FullCharge'],['#check @AspisR1.ARU_Charge.cached_preparation','#check @AspisR1.ART_FullCharge.charged','#print axioms AspisR1.ARU_Charge.cached_preparation']),
('RuntimeRestriction',['ARU_RootRestriction'],['#print AspisR1.F3T_Runtime.StoredCarrierBinding','#check @AspisR1.ARU_RootRestriction.impossible_if_native','#check @AspisR1.ART_RootObstruction.independent','#print axioms AspisR1.ARU_RootRestriction.impossible_if_native']),
('OriginalLaw',['ARU_IndexedOriginalLaw','ARU_OriginalAverage'],['#check @AspisR1.ARU_IndexedOriginalLaw.original_law','#check @AspisR1.ARU_OriginalAverage.averaged','#print axioms AspisR1.ARU_IndexedOriginalLaw.original_law','#print axioms AspisR1.ARU_OriginalAverage.averaged']),
('Domination',['ARU_Domination','ARU_RuntimeMass'],['#check @AspisR1.ARU_Domination.pointwise','#check @AspisR1.ARU_RuntimeMass.pointwise','#print axioms AspisR1.ARU_Domination.pointwise']),
('AllWorldMean',['ARU_Range'],['#check @AspisR1.ARU_Mass.conditional','#check @AspisR1.ARU_Numeric.conditional','#check @AspisR1.ARU_Range.conditional','#print axioms AspisR1.ARU_Numeric.conditional']),
('FinishOwners',['ARU_Join'],['#print AspisR1.FIp_GlobalOwners.Owners','#print AspisR1.FIp_Remaining.Holds','#check @AspisR1.ARU_Join.accepted','#print axioms AspisR1.ARU_Join.accepted']),
('Nonvacuity',['ARU_Nonvacuity'],['#check @AspisR1.ARU_Nonvacuity.conditional','#check AspisR1.JFx_NativeBytes.publicBytes','#check AspisR1.JFx_NativeBytes.proofBytes','#print axioms AspisR1.ARU_Nonvacuity.conditional']),
('FrozenConstants',['ARU_Range','ART_ZeroArithmetic'],['#print AspisR1.F3T_Numeric.total','#print AspisR1.F3T_Numeric.accountLoss','#check AspisR1.ART_ZeroArithmetic.margin','#print axioms AspisR1.ART_ZeroArithmetic.margin','#print axioms AspisR1.ART_ZeroArithmetic.positive']),
('RejectedPrefixes',['ART_RuntimeDomination','ART_QueriedPieces','ART_RejectedNative'],['#check @AspisR1.ART_RuntimeDomination.averaged','#check @AspisR1.ART_QueriedPieces.chronology','#check @AspisR1.ART_RejectedNative.mass','#print axioms AspisR1.ART_RuntimeDomination.averaged']),
('RootScope',['ARU_RootRestriction','Rc10_Top'],['#print AspisR1.ARU_RootRestriction.WithoutBinding','#check @AspisR1.Rc10_Top.deployed','#print axioms AspisR1.Rc10_Top.deployed']),
]
for n,(name,imports,cmds) in enumerate(plan,80):
 m='ARU_Audit'+name
 (r/'lean'/(m+'.lean')).write_text(''.join('import '+i+'\n' for i in imports)+'''set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
'''+ '\n'.join(cmds)+'\n')
(p/'ARU_AUDIT_PLAN.json').write_text(json.dumps([{'attempt':80+i,'module':'ARU_Audit'+x[0],'purpose':x[0]} for i,x in enumerate(plan)],indent=2)+'\n')
