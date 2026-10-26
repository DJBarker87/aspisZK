"""Generate focused statement/field audits, not proof or build infrastructure."""
from pathlib import Path
import json,subprocess
ROOT=Path(__file__).resolve().parents[2]
p=Path(__file__).resolve().parent
specs=[
 ('BeforeAfter',['#check @AspisR1.Rc2_Top.deployed','#check @AspisR1.Rc3_CompatibleTop.deployed','#check @AspisR1.Rc3_Top.deployed','#print AspisR1.Rc3_Result.Outcome']),
 ('Sdk',['#print AspisR1.S2Trust.S2TrustedSdkBorrow']),
 ('Std',['#print AspisR1.S2W_TrustedStd.TrustedStd']),
 ('Allocator',['#print AspisR1.S2W_D189Wrappers.Allocator']),
 ('Extraction',['#print AspisR1.S2W_DigestExtraction.AeneasExtraction']),
 ('Entry',['#print AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission','#print AspisR1.AdapterRw.RuntimeEntrypointAdmission']),
 ('P1',['#print AspisR1.S2W_ExtractionBoundary.P1','#print AspisR1.S2W_ExtractionBoundary.RuntimeSyscall']),
 ('Children',['#print AspisR1.S2W_ExpandedChildren.ChildConeJoin','#print AspisR1.S2W_TraceSplice.FirstMarks','#print AspisR1.S2W_TraceSplice.SecondMarks']),
 ('Cuts',['#print AspisR1.S2W_AuthenticatedInputs.CheckpointWriterConeJoin','#print AspisR1.S2W_AuthenticatedInputs.CheckpointReaderConeJoin']),
 ('History',['#print AspisR1.S2X.CheckpointVersionBinding','#print AspisR1.S2W_AuthenticatedInputs.P2Prime']),
 ('OtherCones',['#print AspisR1.S2W_ChildJoins.FirstEntryVerifierConeJoin','#print AspisR1.S2W_ChildJoins.MultiproofConeJoin','#print AspisR1.S2W_ChildJoins.S8StageConeJoin']),
 ('RoundValues',['#print AspisR1.RowFinish_Control.RoundValues']),
 ('Pairing',['#print AspisR1.Port4D_Pairing.PairingLaws','#print AspisR1.Port4D_Pairing.RoundLaws']),
 ('Semantic',['#print AspisR1.R3SemanticRemainingJoins.EquationEndpoint']),
 ('Matching',['#print AspisR1.MatchingSupport.match0']),
 ('Dot',['#print AspisR1.SAP_FinishSaved.Outcome']),
 ('OldFinish',['#print AspisR1.T2R_Finish.Outcome']),
 ('OldTen',['#print AspisR1.T2R_Ten.Outcome']),
 ('OldContinuation',['#print AspisR1.T2R_CallerSource.Outcome','#print AspisR1.T2R_ContSource.Outcome']),
 ('NewContinuation',['#print AspisR1.SAP_LiteralCaller.Outcome','#print AspisR1.SAP_LiteralCont.Outcome']),
 ('Primitive',['#print AspisR1.Port5Q1_QueryPorts.SessionAPrimitives']),
 ('Basis',['#print AspisR1.Port4C_BasisOuter.SessionABasis']),
 ('Arithmetic',['#print AspisR1.Port4C_QueryArithmetic.SessionABackends']),
 ('M31',['#print AspisR1.Port5Q1_NodeModel.SessionAM31']),
 ('Opening',['#print AspisR1.Port5Q1_OpeningValues.SessionAS3']),
 ('QueryOps',['#print AspisR1.Port3_NativeQueryBody.Ops']),
 ('GeoLeaves',['#print AspisR1.Port5Q1_GeometryCanonical.SessionAPrimitives']),
 ('Domain',['#print AspisR1.Port5Q1_Domain.SessionADomain']),
 ('GeoOps',['#print AspisR1.Port3_NativeGeometryBody.Ops']),
 ('SourceGeometry',['#print AspisR1.Port4C_InverseExecution.inverse_owned']),
 ('GeoGuards',['#print AspisR1.SAP_LiteralOutcome.Outcome']),
 ('PrepareBefore',['#print AspisR1.WAdm_Domain.SessionAPrepare','#print AspisR1.Port5Q2_Prepared.PreparedFields']),
 ('PrepareAfter',['#check @AspisR1.SAP_PrepareOwner.installed','#check @AspisR1.SAP_Binding.prepare']),
 ('PrepareSpecialized',['#print AspisR1.Port5Q1_QueryPorts.SessionAPrepare','#print AspisR1.SAP_LiteralFields.Fields']),
 ('Numeric',['#print AspisR1.SAP_CurrentNumeric.numeric','#check @AspisR1.SAP_NumericTransport.numeric']),
 ('Association',['#check @AspisR1.SAP_DataAssociation.associate','#check @AspisR1.SAP_InputUnique.unique']),
 ('Discovery',['#check @AspisR1.SAP_Discovery.from_cut','#check @AspisR1.SAP_BindingUnique.queries','#check @AspisR1.SAP_BindingUnique.context']),
 ('Configuration',['#print AspisR1.DrvC_Installation.Configuration','#print AspisR1.Rc3_Install.configuration','#check @AspisR1.Rc3_Install.compatible','#check @AspisR1.Rc3_Install.exact_scope']),
 ('Dictionary',['#print AspisR1.DrvC_FirstConstants.configuration','#print AspisR1.SAP_Install.configuration','#check @AspisR1.Rc3_Install.dictionary']),
 ('NP6',['#print AspisR1.NP6_StdModel.calls','#print AspisR1.NP6_Constructors.Contents','#print AspisR1.NP6_ClaimsRun.Content','#print AspisR1.NP6_ParsedClaims.Content']),
 ('Base',['#print AspisR1.Rc2_Base.Outcome','#check @AspisR1.Rc2_Base.strengthen']),
 ('Events',['#print AspisR1.Rc2_Events.Facts']),
 ('Protection',['#print AspisR1.Rc2_Protection.Facts']),
 ('Nonvacuity',['#print AspisR1.Rc3_Nonvacuity.Facts','#check @AspisR1.Rc3_Nonvacuity.derive','#print AspisR1.T2R_Acceptance.Facts']),
 ('Physical',['#print AspisR1.T2R_Public.Facts','#print AspisR1.T2R_Parser.Facts']),
 ('OldRaw',['#print AspisR1.OraclePortFrozen2Join.AcceptedRunJoin','#print AspisR1.Port1_CanonicalJoin.AcceptedRunJoin']),
 ('Library',['#print AspisR1.S2Trust.Library','#print AspisR1.Port1_Library.TrustedStd']),
 ('Carriers',['#print AspisR1.R1FinalSoundness.SourceInputs','#print AspisR1.MatchingSupport.Data','#print AspisR1.OraclePortCompactDraft.Parsed']),
 ('Model',['#print AspisR1.F3_Model.Input','#print AspisR1.OraclePortCheckpointResumeC5.Context']),
 ('Sampler',['#print AspisR1.F3J_SamplerRun.program','#print AspisR1.CanonicalCutEnrichedTranscript.Words']),
 ('FullEquality',['#check @AspisR1.SAP_LiteralConsumer.literal','#check @AspisR1.SAP_FinishSaved.consume','#check @AspisR1.SAP_CloseConsumer.close']),
 ('FinalAxioms',['#print axioms AspisR1.Rc3_Top.deployed','#print axioms AspisR1.Rc3_CompatibleTop.deployed','#print axioms AspisR1.Rc3_Nonvacuity.derive','#print axioms AspisR1.Rc3_Install.compatible','#print axioms AspisR1.Rc3_Install.exact_scope','#print axioms AspisR1.Rc3_Install.dictionary'])
]
assert len(specs)==52,len(specs)
for n,(name,commands) in enumerate(specs,9):
 if n > 20: break # mandatory host stop at reservation barrier for attempt21
 module=f'Rc3_Audit{name}'
 source='''import Rc3_Top
import Rc3_CompatibleTop
import SAP_DataAssociation
import SAP_InputUnique
import SAP_BindingUnique
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
'''+ '\n'.join(commands)+'\n'
 (ROOT/'lean'/f'{module}.lean').write_text(source)
 x=json.loads((p/'Rc3_008.json').read_text());x.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),attempt=f'Rc3_{n:03}',sources=[module+'.lean']);x['command'][-2:]=[module+'.olean',module+'.lean'];x['expected_time']='Fresh bounded ledger statement expansion: '+name
 (p/(x['attempt']+'.json')).write_text(json.dumps(x,indent=2)+'\n')
