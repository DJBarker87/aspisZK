"""Literal legacy-model fission mirroring the already receipted source suffixes.
Only namespace/type/callee substitutions listed here; Lean source theorem checks
that fission folds to the exact CLOSED179 semantic-domain model.
"""
from pathlib import Path
import re,hashlib,json
E=Path(__file__).resolve().parent
source=(E/'NNG_SourceSuffixes.lean').read_text()
s=source.replace('import NNG_EmittedContext','import LIBC_PreparedDomain\nimport NNG_Model134')
s=s.replace('namespace AspisR1.NNG_SourceSuffixes','namespace AspisR1.NNG_LegacySuffix136').replace('end AspisR1.NNG_SourceSuffixes','end AspisR1.NNG_LegacySuffix136')
s=s.replace('open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted','open Aeneas Aeneas.Std Result AspisR1PublicPreparation')
a=s.index('\ndef f_')
carriers='''
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Claims := Array (Array Q 29#usize) 3#usize
abbrev K29 := Array Q 29#usize
abbrev Output (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error
structure Parent (H W : Type) where
 digest : aspis_core.Digest32 H
 publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public
 prefixValue : r1_wire.Prefix
 transcript : r1_wire.SemanticTranscript H
 challenges : r1_wire.Challenges
 observer : Option (RPz7_PhaseIso.Phase → Result Unit)
'''
s=s[:a]+'\n'+carriers+s[a:]
s=s.replace('(c : Calls)','(B : FinishModel.Boundaries)').replace(' c s',' B s')
s=s.replace('aspis_core.state_only_prefix.r0.Challenges','r1_wire.Challenges')
s=s.replace('(aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c.c3)','aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31')
s=s.replace('r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31','FinishModel.closureFn5').replace('r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31','FinishModel.closureFn9').replace('r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError','FinishModel.closureFn11')
s=s.replace('core.result.Result.unwrap\n      core.fmt.DebugTryFromSliceError r11','B.unwrapRoot r11')
replace={10:'RoundModel.rounds AspisS1ExtractedRoundChildren.children',8:'B.claims',7:'B.terminal',6:'B.mask',11:'r1_wire.Prefix.validated_record',15:'AspisS1ExtractedRoundChildren.children.decode',5:'B.mul',4:'B.add',14:'r1_wire.SemanticTranscript.impl.state',13:'FinishModel.circle_validated B',12:'FinishModel.payload',2:'FinishModel.pointEq',0:'B.fromFn',1:'core.result.Result.map_err',9:'VerifyPrefix.mark'}
for i,f in replace.items():s=re.sub(r'\bc\.c'+str(i)+r'\b',f,s)
assert not re.search(r'\bc\.',s)
root='''
theorem source {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) :
 f_r B s = FinishModel.finish AspisS1ExtractedRoundChildren.children B s.digest s.publicValue s.prefixValue s.transcript s.challenges s.observer := by
 rfl
#print axioms source
'''
s=s.replace('end AspisR1.NNG_LegacySuffix136',root+'end AspisR1.NNG_LegacySuffix136')
(E/'NNG_LegacySuffix136.lean').write_text(s)
(E/'NNG_LEGACY_FISSION_PINS.json').write_text(json.dumps({'input':'NNG_SourceSuffixes.lean','sha256':hashlib.sha256(source.encode()).hexdigest(),'output_sha256':hashlib.sha256(s.encode()).hexdigest(),'callee_substitutions':replace,'purpose':'Exact model-side fission, no native-credit claim; source theorem checked by Lean'},indent=1)+'\n')
