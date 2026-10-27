"""Generate focused statement audits, not build infrastructure."""
from pathlib import Path
import json
P=Path(__file__).resolve().parent;R=P.parents[1]
specs=[
('BeforeAfter',['#check @AspisR1.Rc3_Top.deployed','#check @AspisR1.Rc4_Top.deployed','#check @AspisR1.SAQ_CompleteTop.deployed','#check @AspisR1.TxS_Top.deployed']),
('Statement',['#print AspisR1.Rc4_Statement.Conclusion']),
('Result',['#print AspisR1.Rc4_Result.Outcome','#check @AspisR1.Rc4_ResultForget.forget']),
('Continuation',['#print AspisR1.Rc4_Caller.Outcome','#print AspisR1.Rc4_Cont.Outcome']),
('Literal',['#print AspisR1.Rc4_Literal.Outcome','#check @AspisR1.Rc4_LiteralForget.forget']),
('RawCarriers',['#print AspisR1.Rc4_Model.Input','#print AspisR1.Rc4_Model.typed','#print AspisR1.TxS_Carriers.Metadata','#print AspisR1.TxS_Carriers.source','#print AspisR1.TxS_Carriers.data','#print AspisR1.TxS_Carriers.toTyped']),
('OldCarriers',['#print AspisR1.F3_Model.Input','#print AspisR1.F3_Model.SemanticPublic','#print AspisR1.R1FinalSoundness.SourceInputs','#print AspisR1.MatchingSupport.Data']),
('Primitive',['#print AspisR1.Port5Q1_QueryPorts.SessionAPrimitives','#check @AspisR1.SAQ_Decoder.primitives']),
('BasisArithmetic',['#print AspisR1.Port4C_BasisOuter.SessionABasis','#print AspisR1.Port4C_QueryArithmetic.SessionABackends']),
('M31Opening',['#print AspisR1.Port5Q1_NodeModel.SessionAM31','#print AspisR1.Port5Q1_OpeningValues.SessionAS3']),
('GeometryDomain',['#print AspisR1.Port5Q1_GeometryCanonical.SessionAPrimitives','#print AspisR1.Port5Q1_Domain.SessionADomain']),
('OldLiteral',['#print AspisR1.SAP_LiteralOutcome.Outcome','#print AspisR1.SAP_LiteralCont.Outcome']),
('Finish',['#print AspisR1.SAP_FinishSaved.Outcome','#print AspisR1.RowFinish_Control.RoundValues']),
('FinishLaws',['#print AspisR1.Port4D_Pairing.PairingLaws','#print AspisR1.Port4D_Pairing.RoundLaws','#print AspisR1.R3SemanticRemainingJoins.EquationEndpoint','#print AspisR1.MatchingSupport.match0']),
('Nonvacuity',['#print AspisR1.Rc3_Nonvacuity.Facts','#check @AspisR1.Rc4_Nonvacuity.contracts','#check @AspisR1.Rc4_Nonvacuity.model_surjective','#check @AspisR1.Rc4_Nonvacuity.data_surjective','#print AspisR1.T2R_Acceptance.Facts']),
('Sdk',['#print AspisR1.S2Trust.S2TrustedSdkBorrow']),
('Std',['#print AspisR1.S2W_TrustedStd.TrustedStd','#print AspisR1.S2Trust.Library']),
('Allocator',['#print AspisR1.S2W_D189Wrappers.Allocator']),
('Extraction',['#print AspisR1.S2W_DigestExtraction.AeneasExtraction']),
('Entry',['#print AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission','#print AspisR1.AdapterRw.RuntimeEntrypointAdmission']),
('Oracle',['#print AspisR1.S2W_ExtractionBoundary.P1','#print AspisR1.S2W_ExtractionBoundary.RuntimeSyscall']),
('Children',['#print AspisR1.S2W_ExpandedChildren.ChildConeJoin','#print AspisR1.S2W_TraceSplice.FirstMarks','#print AspisR1.S2W_TraceSplice.SecondMarks']),
('Cuts',['#print AspisR1.S2W_AuthenticatedInputs.CheckpointWriterConeJoin','#print AspisR1.S2W_AuthenticatedInputs.CheckpointReaderConeJoin']),
('History',['#print AspisR1.S2X.CheckpointVersionBinding','#print AspisR1.S2W_AuthenticatedInputs.P2Prime']),
('OtherCones',['#print AspisR1.S2W_ChildJoins.FirstEntryVerifierConeJoin','#print AspisR1.S2W_ChildJoins.MultiproofConeJoin','#print AspisR1.S2W_ChildJoins.S8StageConeJoin']),
('NP6',['#print AspisR1.NP6_Constructors.Contents','#print AspisR1.NP6_ClaimsRun.Content','#print AspisR1.NP6_ParsedClaims.Content']),
('Bank',['#print AspisR1.Rc2_Events.Facts','#print AspisR1.Rc2_Protection.Facts']),
('Configuration',['#print AspisR1.Rc4_Install.configuration','#print AspisR1.SAQ_CompleteInstall.select','#check @AspisR1.Rc4_Install.exact_scope','#check @AspisR1.Rc4_Install.saq','#check @AspisR1.Rc4_Install.rc3']),
('Slots',['#print AspisR1.Port3_NativeQueryBody.Ops','#print AspisR1.Port3_NativeGeometryBody.Ops','#print AspisR1.SAQ_Decoder.install','#print AspisR1.SAQ_Constructor.install']),
('RawJoin',['#print AspisR1.OraclePortFrozen2Join.AcceptedRunJoin','#print AspisR1.Port1_CanonicalJoin.AcceptedRunJoin','#print AspisR1.OraclePortRuntimeBindingC7.StoredCarrierBinding']),
('P6Boundary',['#print AspisR1.MultiproofConeP6Frozen2Stage.P6Boundary']),
('Axioms',['#print axioms AspisR1.Rc4_Top.deployed','#print axioms AspisR1.Rc4_Assemble.deployed','#print axioms AspisR1.Rc4_Result.strengthen','#print axioms AspisR1.Rc4_ResultForget.forget','#print axioms AspisR1.Rc4_Literal.strengthen','#print axioms AspisR1.Rc4_LiteralForget.forget','#print axioms AspisR1.Rc4_Encoding.derive','#print axioms AspisR1.Rc4_Model.typed_erase','#print axioms AspisR1.Rc4_Nonvacuity.contracts']),
('ParserEncoding',['#print AspisR1.T2R_Parser.Facts','#print AspisR1.TxS_Encoding.Facts','#print AspisR1.TxS_RawPublic.Facts','#print AspisR1.SAQ_Decoder.read','#print AspisR1.SAQ_Constructor.fibre'])]
assert len(specs)==33
plan=[]
for n,(name,commands) in enumerate(specs,28):
 m='Rc4_Audit'+name
 text='''import Rc4_Top
import Rc4_ResultForget
import Rc4_Nonvacuity
import SAQ_CompleteTop
import TxS_Top
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
'''+ '\n'.join(commands)+'\n'
 (R/'lean'/(m+'.lean')).write_text(text)
 plan.append(dict(attempt=f'Rc4_{n:03}',module=m,commands=commands))
(P/'Rc4_audit_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
