"""Round 2 of X5: the base modules now declare the seven names under their ORIGINAL names.
Revert every constant site and every RecordedBinaryExperimentBin open line of round 1 to the original text;
keep import lines, the raw (AspisHonestBudgetBase) open lines and the AspisRowStarts/AspisRowStarts33 split.
Each replacement asserts its exact occurrence count."""
import sys,re
d=sys.argv[1]
RB='AspisR1.AspisLib.RecordedBinaryExperimentBin'
E=[
 ('AspisRows40Starts',f'open {RB} RawCutProverCompiler DecodedFirstReadUnionBound\n','open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound\n',1),
 ('AspisRows40Starts',f'  unfold {RB}.dec RawAdaptiveLiteralDecoder.decode\n','  unfold RecordedBinaryExperimentBin.dec RawAdaptiveLiteralDecoder.decode\n',1),
 ('AspisRowStarts40',f'open {RB} RawCutProverCompiler DecodedFirstReadUnionBound\n','open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound\n',1),
 ('AspisCharge40',f'    cases hdec : {RB}.dec a T with\n','    cases hdec : RecordedBinaryExperimentBin.dec a T with\n',1),
 ('AspisRec40ChargePrefix','  have hp := AspisR1.AspisLib.DecoderQueryAccounting.starts_le_queries','  have hp := DecoderQueryAccounting.starts_le_queries',1),
 ('AspisChargedWeight40',f'open AspisR1 {RB} DecodedFirstReadUnionBound\n','open AspisR1 RecordedBinaryExperimentBin DecodedFirstReadUnionBound\n',1),
 ('AspisChargedWeight40','  have hc := AspisR1.AspisLib.DecoderQueryAccounting.starts_le_queries','  have hc := DecoderQueryAccounting.starts_le_queries',1),
 ('AspisRec40CallBudget','    (hq : AspisR1.AspisLib.DecoderQueryAccounting.AdversaryQueries P Q)','    (hq : DecoderQueryAccounting.AdversaryQueries P Q)',1),
 ('AspisOneTxDecision','AspisR1.AspisLib.OraclePortAdmission.Guard','OraclePortAdmission.Guard',2),
 ('AspisOneTxChecks','AspisR1.AspisLib.OraclePortAdmission.Guard','OraclePortAdmission.Guard',3),
 ('AspisRec40CleanTag','AspisR1.AspisLib.OraclePortAdmission.Guard','OraclePortAdmission.Guard',1),
 ('AspisRec40CleanTag','AspisR1.AspisLib.InitialTagDecision.erased_transcript_tag','InitialTagDecision.erased_transcript_tag',1),
 ('AspisRec40CleanStatement',f'{RB}.binaryCollision','RecordedBinaryExperimentBin.binaryCollision',2),
 ('AspisRec40Clean',f'{RB}.binaryCollision','RecordedBinaryExperimentBin.binaryCollision',4),
 ('AspisOneTxCheckedAcceptance',f'{RB}.binaryCollision','RecordedBinaryExperimentBin.binaryCollision',3),
 ('AspisFailureBound',f'{RB}.binaryCollision','RecordedBinaryExperimentBin.binaryCollision',6),
 ('AspisRec40CleanRun','    rw [AspisRows40.Starts.decAspis_of_r1 _ _ _\n      (by rw [show AspisR1.AspisLib.RecordedBinaryExperimentBin.dec _ _ = _ from hdec]; simp)]\n',
                       '    rw [AspisRows40.Starts.decAspis_of_r1 _ _ _ (by rw [hdec]; simp)]\n',1),
 # AspisRowStarts: restore the original open lines (BinHonestQueryBudget -> AspisHonestBudgetBase, the raw base),
 # import AspisHonestBudgetBase (which imports BinHonestStartFrames) and AspisLib_Recorded (namespace of the open),
 # and drop the round-1 doc note so that only imports, the raw open and the moved declarations differ.
 ('AspisRowStarts','import BinHonestStartFrames\n','import AspisHonestBudgetBase\nimport AspisLib_Recorded\n',1),
 ('AspisRowStarts','open RawCutProverCompiler DecodedFirstReadUnionBound\nopen BinHonestStartFrames\n',
                   'open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound\nopen BinHonestStartFrames AspisHonestBudgetBase\n',1),
 ('AspisRowStarts',"not determined here).\n\nThe sampler-row theorems about R1's 33-row decoder (`sampler_weight`,\n`row_weight`, `rows_weight`, `verifier_weight`) are in `AspisRowStarts33`,\nin this namespace. -/",
                   'not determined here). -/',1),
]
for f,old,new,n in E:
    p=f'{d}/{f}.lean'; t=open(p).read(); c=t.count(old)
    assert c==n,(f,old,c,n)
    open(p,'w').write(t.replace(old,new)); print('ok',f,n)
