from pathlib import Path
import re
s=Path('lean/Cons_Pair.lean').read_text()
imports=s[:s.index('set_option')].replace('import Cons_Ten','import Cons_Pair')
header=s[s.index('set_option'):s.index('/-- The union')].replace('AspisR1.Cons_Pair','AspisR1.Cons_Top')
sig=s[s.index('theorem accepted'):s.index(' := by\n  obtain')]
a=sig.index('    (adapterOps :'); b=sig.index(' (native1 :',a)
sig=sig[:a]+'    (c : DrvC_Installation.Configuration F CoreError)\n   '+sig[b:]
# after removing all dictionary argument binders, specialize every occurrence
mapping={'adapterOps':'adapter','ops':'currentBase','reserved':'reserved','queryOps':'query','geoOps':'geometry','stageBase':'stageBase','finishOps':'finish','B':'boundaries','claimsStd':'std'}
for n,field in mapping.items():sig=re.sub(r'\b'+n+r'\b',f'(DrvC_FirstConstants.configuration c).{field}',sig)
sig=sig.replace('theorem accepted','theorem deployed')
sig=sig.replace('    (prior : Program Bytes State Unit)\n','')
a=sig.index('    :\n'); params=sig[:a]
pair=sig[a+len('    :\n'):]
h=Path('lean/DrvC_SourceHeadline.lean').read_text()
ha=h.index('    (D :');hb=h.index(' :\n    let r :=',ha)
hparams=h[ha:hb]
# hashv already exists on native side
hparams=re.sub(r'    \(hashv : SdkC_Source.Parts → Result SdkC_Source.Digest\)\n','',hparams)
hparams=hparams.replace('    (D :','    (prior : Program Bytes State Unit)\n    (D :')
hresult=h[hb+len(' :\n'):h.index(' := by',hb)]
result='''    DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) =
      DrvC_SourceEntry.source (DrvC_FirstConstants.configuration c) hashv ∧
    DrvC_Installation.sdk (DrvC_FirstConstants.configuration c) =
      SdkD_PairBatches.dictionary (DrvC_FirstConstants.configuration c).adapter
        (DrvC_FirstConstants.configuration c).currentBase (DrvC_FirstConstants.configuration c).stageBase
        (DrvC_FirstConstants.configuration c).finish (DrvC_FirstConstants.configuration c).reserved
        (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry
        (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std ∧
    ('''+hresult.strip()+''') ∧
    ('''+pair.strip()+''')'''
proof=''' := by
  refine ⟨DrvC_SourceEntry.same_program c hashv,
    DrvC_Installation.aus1_dictionary (DrvC_FirstConstants.configuration c),?_,?_⟩
  · exact DrvC_SourceHeadline.deployed_headline_source c D P Q0 Q1 hqueries hashv runtime raw binding
      adversary chooseSecond prefixBound choiceBound project
  · exact Cons_Pair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      (DrvC_FirstConstants.configuration c).adapter (DrvC_FirstConstants.configuration c).currentBase
      (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query
      (DrvC_FirstConstants.configuration c).geometry (DrvC_FirstConstants.configuration c).stageBase
      (DrvC_FirstConstants.configuration c).finish (DrvC_FirstConstants.configuration c).boundaries
      (DrvC_FirstConstants.configuration c).std native1 native2 prepareOwner primitiveOwner hashv extraction
      prior sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 p root length

#print axioms deployed
end AspisR1.Cons_Top
end
'''
# additional opens used by headline
header=header.replace('open scoped BigOperators','open OraclePortRuntimeBindingC7 Port1_StoredCarrier\nopen OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)\nopen scoped BigOperators')
Path('lean/Cons_Top.lean').write_text(imports+header+params+'\n'+hparams+' :\n'+result+proof)
