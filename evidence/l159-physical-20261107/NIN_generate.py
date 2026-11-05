"""Compose unchanged packet binder interfaces; generated targets are NIN-only."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
P=E.parent/'carriers-bind-20261105'/'NGS_PersistedCarriers.lean'
s=P.read_text();sig=s[s.index('theorem saved_to_carriers'):s.index(' :\n    (bytesOf s.proof.val')]
sig=sig.replace('theorem saved_to_carriers','theorem physical_instance')
pool=(E.parent/'pool-settle-20261106'/'NIB_ReadToSettlement.lean').read_text()
poolSig=pool[pool.index('    {Invocation Context'):pool.index(' :\n    validate_pool')]
sig+='\n'+poolSig.replace('(runtime : Runtime ', '(runtime : NGK_NFO_PoolReturnData.Runtime ')
# All Pool observations use the SAME response-selected verifier entry.
sig+='''
    (verifierEntry : Invocation → Entry)
    (sameVerifierEntry : verifierEntry emitInvocation =
      (((eval H source).2).2.2.get reached).1.entry) :
    (NGP_L159.L159_statement p t u
      (NIN_Cuts.of_producers f s (((eval H source).2).2.2.get reached).1.entry
        prepared accumulator domain hp hu hc s_1 authenticated)
      Q (eval H (Hiq_RecordedJoint.program source ARQ_Observer.project
        (ARQ_Observer.select cfg id)))) ∧
    verifierEntry poolInvocation = CPG_Projection.entry p u := by
'''
# Pool statement's `s` conflicts with SecondCut; give the statement a separate name.
sig=sig.replace('(s : NFY_NEU_EmitModel.Statement)','(emittedStatement : NFY_NEU_EmitModel.Statement)')
# Rename only Pool-local signature occurrences.
start=sig.index('    {Invocation Context')
a,b=sig[:start],sig[start:]
import re
b=re.sub(r'\bs\b','emittedStatement',b)
b=b.replace('of_producers f emittedStatement','of_producers f s').replace('s_1 authenticated','emittedStatement authenticated')
sig=a+b
sig=sig.replace('(data1 : Slice U8) (state1 final1 : A)', '(final1 : A)')
sig=re.sub(r'\bdata1\b', '((eval H source).2).1.data', sig)
sig=re.sub(r'\bstate1\b', '((eval H source).2).1.state', sig)
header=s[:s.index('/-- Direct NGR')].replace('import NGS_Carriers','import NIN_Cuts\nimport NIB_ReadToSettlement').replace('AspisR1.NGS_CARRIERS','AspisR1.NIN_PhysicalInstance')
body='''  let cuts := NIN_Cuts.of_producers f s (((eval H source).2).2.2.get reached).1.entry
    prepared accumulator domain hp hu hc emittedStatement authenticated
  have history : NGP_L159.History_statement p t u cuts := by
    exact NGR_HISTORY.history_statement prepared accumulator domain hp hu hc p t u
      ((eval H source).2).1.entry (((eval H source).2).2.2.get reached).1.entry
      actions n1 n2 copy std allocator valid1 id system data1 state1 final1 post1
      game native_writer_result protection ordinary RuntimePersistence L sdk w2 related2 valid2 cuts
  have carriers := NGS_CARRIERS.saved_to_carriers base err r hashv copy allocator a H
    Q bound reached prepared accumulator domain hp hu hc p t u n1 n2 actions std valid1
    system data1 state1 final1 post1 game native_writer_result protection ordinary
    RuntimePersistence L sdk w2 related2 valid2 f s finish1 proof1Index public1Index
    proof1Read public1Read range1 length1 proof2Index proof2Read range2 length2
    v validation encoding writerResult checkpoint2Index checkpoint2Read readerResult
  have pool := NIB_ReadToSettlement.read_to_settlement runtime law emitInvocation poolInvocation
    context program selected readState state after emittedStatement sameCpi selectedProgram
    noInterveningCpi emitted authenticated events acceptedDecoder validate lane image checked advanced
  exact ⟨⟨history,NIN_Cuts.carrier_or_collision f s
    (((eval H source).2).2.2.get reached).1.entry prepared accumulator domain hp hu hc
    emittedStatement authenticated Q _ carriers pool.2.2.2.2.1 pool.2.2.2.1⟩,
    (congrArg verifierEntry sameCpi).trans (sameVerifierEntry.trans game.consecutive.2.2)⟩

#print axioms physical_instance
end
end AspisR1.NIN_PhysicalInstance
end
'''
body=re.sub(r'\bdata1\b', '((eval H source).2).1.data', body)
body=re.sub(r'\bstate1\b', '((eval H source).2).1.state', body)
(E/'NIN_PhysicalInstance.lean').write_text(header+'''/-- Universal conditional model instance on the SAME response-selected entries.
No freely chosen Cuts, history equality, carrier equality, or recorder is an input.
The Pool-entry projection is an OPEN native association, not an accepted trust row.
The entry-association binder also maps the SAME Pool invocation to game u. -/
'''+sig+body)
(E/'NIN_GENERATOR_PROVENANCE.json').write_text(json.dumps(dict(inputs=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in [P,E.parent/'pool-settle-20261106'/'NIB_ReadToSettlement.lean']],method='Copy exact typed packet interfaces, rename local statement binder, compose original packet theorems; no packet source edited'),indent=1)+'\n')
