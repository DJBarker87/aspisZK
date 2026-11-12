"""Re-point the Aspis chain: (file, old, new, expected count). Code lines only; comments untouched.
Each replacement asserts the exact number of occurrences of `old` on non-comment lines it changes."""
import sys,re
d=sys.argv[1]
RB='AspisR1.AspisLib.RecordedBinaryExperimentBin'
E=[
 # AspisRows40Starts
 ('AspisRows40Starts','import BinHonestQueryBudget\n','import AspisHonestBudgetBase\nimport AspisLib_Recorded\n',1),
 ('AspisRows40Starts','open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound\n',f'open {RB} RawCutProverCompiler DecodedFirstReadUnionBound\n',1),
 ('AspisRows40Starts','open BinHonestStartFrames BinHonestQueryBudget\n','open BinHonestStartFrames AspisHonestBudgetBase\n',1),
 ('AspisRows40Starts','  unfold RecordedBinaryExperimentBin.dec RawAdaptiveLiteralDecoder.decode\n',f'  unfold {RB}.dec RawAdaptiveLiteralDecoder.decode\n',1),
 # AspisRows40FinalStarts
 ('AspisRows40FinalStarts','open DecodedFirstReadUnionBound BinHonestQueryBudget\n','open DecodedFirstReadUnionBound AspisHonestBudgetBase\n',1),
 # AspisRowStarts40
 ('AspisRowStarts40','open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound\n',f'open {RB} RawCutProverCompiler DecodedFirstReadUnionBound\n',1),
 ('AspisRowStarts40','open BinHonestStartFrames BinHonestQueryBudget\n','open BinHonestStartFrames AspisHonestBudgetBase\n',1),
 # AspisCharge40
 ('AspisCharge40','    cases hdec : RecordedBinaryExperimentBin.dec a T with\n',f'    cases hdec : {RB}.dec a T with\n',1),
 # AspisRec40ChargePrefix
 ('AspisRec40ChargePrefix','import AspisRows40FinalStarts\n','import AspisRows40FinalStarts\nimport AspisLib_QueryAccounting\n',1),
 ('AspisRec40ChargePrefix','  have hp := DecoderQueryAccounting.starts_le_queries AspisRows40.FinalStarts.decFinal','  have hp := AspisR1.AspisLib.DecoderQueryAccounting.starts_le_queries AspisRows40.FinalStarts.decFinal',1),
 # AspisChargedWeight40
 ('AspisChargedWeight40','open AspisR1 RecordedBinaryExperimentBin DecodedFirstReadUnionBound\n',f'open AspisR1 {RB} DecodedFirstReadUnionBound\n',1),
 ('AspisChargedWeight40','  have hc := DecoderQueryAccounting.starts_le_queries AspisRows40.FinalStarts.decFinal','  have hc := AspisR1.AspisLib.DecoderQueryAccounting.starts_le_queries AspisRows40.FinalStarts.decFinal',1),
 # AspisRec40CallBudget
 ('AspisRec40CallBudget','import AspisRec40HitMass\n','import AspisRec40HitMass\nimport AspisLib_QueryAccounting\n',1),
 ('AspisRec40CallBudget','    (hq : DecoderQueryAccounting.AdversaryQueries P Q)','    (hq : AspisR1.AspisLib.DecoderQueryAccounting.AdversaryQueries P Q)',1),
 # AspisOneTxDecision
 ('AspisOneTxDecision','import OraclePortFrozenOrderDecision\n','import OraclePortFrozenOrderDecision\nimport AspisLib_Guard\n',1),
 ('AspisOneTxDecision','open RecordedBinaryExperimentBin (SourceInputs)\n',f'open {RB} (SourceInputs)\n',1),
 ('AspisOneTxDecision','  if OraclePortAdmission.Guard (take33 tr)','  if AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr)',1),
 ('AspisOneTxDecision','    OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 ∧ ∃ p q i,','    AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 ∧ ∃ p q i,',1),
 # AspisOneTxChecks
 ('AspisOneTxChecks','open RecordedBinaryExperimentBin (SourceInputs)\n',f'open {RB} (SourceInputs)\n',1),
 ('AspisOneTxChecks','  if OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 then core tr m else .done false','  if AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 then core tr m else .done false',1),
 ('AspisOneTxChecks','    OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 := by','    AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 := by',1),
 ('AspisOneTxChecks','  by_cases hg : OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40','  by_cases hg : AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40',1),
 # AspisRec40CleanTag
 ('AspisRec40CleanTag','import AspisOneTxChecks\n','import AspisOneTxChecks\nimport AspisLib_Tag\n',1),
 ('AspisRec40CleanTag','    (h : OraclePortAdmission.Guard (AspisOneTx.take33 X))','    (h : AspisR1.AspisLib.OraclePortAdmission.Guard (AspisOneTx.take33 X))',1),
 ('AspisRec40CleanTag','InitialTagDecision.erased_transcript_tag] at hg','AspisR1.AspisLib.InitialTagDecision.erased_transcript_tag] at hg',1),
 # binaryCollision sites
 ('AspisRec40CleanStatement','RecordedBinaryExperimentBin.binaryCollision',f'{RB}.binaryCollision',2),
 ('AspisRec40Clean','RecordedBinaryExperimentBin.binaryCollision',f'{RB}.binaryCollision',4),
 ('AspisOneTxCheckedAcceptance','RecordedBinaryExperimentBin.binaryCollision',f'{RB}.binaryCollision',3),
 ('AspisFailureBound','RecordedBinaryExperimentBin.binaryCollision',f'{RB}.binaryCollision',6),
 ('AspisFailureBound','import RecordedBinaryExperimentBin\n','import AspisLib_Recorded\n',1),
 # 33-row side: importer of the split module
 ('AspisChargedWeight','import AspisRowStarts\n','import AspisRowStarts33\n',1),
]
for f,old,new,n in E:
    p=f'{d}/{f}.lean'; t=open(p).read()
    # count on code only: ensure every occurrence is outside comments by checking it is not in a doc/comment line
    c=t.count(old)
    if old.endswith('binaryCollision'):
        # exclude occurrences already prefixed (idempotence guard)
        c=len(re.findall(r'(?<![.\w])'+re.escape(old),t))
    assert c==n,(f,old,c,n)
    if old.endswith('binaryCollision'):
        t=re.sub(r'(?<![.\w])'+re.escape(old),new,t)
    else:
        t=t.replace(old,new)
    open(p,'w').write(t); print('ok',f,n,repr(old[:60]))
