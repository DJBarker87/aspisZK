from pathlib import Path
s=Path('evidence/top-form-20261107/TFM_TopExact.lean').read_text()
a=s.index('theorem top_split (');b=s.index('/-- The split form implies',a)
t=s[a:b].replace('    (er : NNE_EntryRep S L V0 VL I)\n','')
t=t.replace('    (out2 : S.Out2', '    (count1 : (S.args1 c).accounts.length = 3)\n    (count2 : (S.args2 c).accounts.length = 7)\n    (out2 : S.Out2')
t=t.replace('  have stage1Ref :', '''  have route1 := NNE_SelectedRoutes.first L D _ VL P C (S.args1 c) (S.state1 c)
    (S.env1 c) _ count1 (weak _ _ _) ok1
  have route2 := NNE_SelectedRoutes.second L D _ VL P C (S.args2 c) (S.state2 c)
    (S.env2 c) _ count2 (weak _ _ _) ok2
  have stage1Ref :''')
t=t.replace('(er.route1 c frame trace)','route1').replace('(er.route2 c frame trace)','route2')
header='''import NNE_SelectedRoutes
import NNE_RecordSig
import TFM_TopExact
set_option autoImplicit false
namespace NNE_TopSplit
open RSL RSL.TAS RSL.TFM
open RSL.TX2_241 (V2Lib)
open RSL.TX1_345 (S1Lib)
/- Same split form as TFM, deriving selected routes from the already required
actual Ok observations and the concrete account counts. TAS.EntryRep's field
omits Ok; this theorem needs no stronger physical-trace premise to repair it.
No adopted-headline or security-number claim is made. -/
'''
Path('evidence/phys-adapter-20261111/NNE_TopSplit.lean').write_text(header+t+'\n#print axioms top_split\nend NNE_TopSplit\n')
# Specialize the same theorem to literal physical definitions and constructed packets.
t2=t[:t.index(' := by')]
t2=t2.replace('theorem top_split (S : Sig)', '''theorem physical_top_split (base : Sig) (d : NNE_AcceptanceSig.Data base)
    (r : NNE_RecordSig.Data base)''')
t2=t2.replace('    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)\n','')
t2=t2.replace('    (count1 : (S.args1 c).accounts.length = 3)\n    (count2 : (S.args2 c).accounts.length = 7)\n','')
# S is a local notation expanded into the concrete physical Sig.
t2=t2.replace(' S)', ' (NNE_RecordSig.physical base d r))').replace(' S ', ' (NNE_RecordSig.physical base d r) ').replace('S.', '(NNE_RecordSig.physical base d r).')
body=''' := by
 apply top_split (NNE_RecordSig.physical base d r) L D V0 VL P C I sp hl a0
   nmm nmx nms nmv nmw nmt nmp nmo nmn g1a nmf cs r0 a1 a2
   (NNE_RecordSig.a3 base d r VL P C) (NNE_RecordSig.a4 base d r L D V0)
   (NNE_RecordSig.a5 base d r L V0 VL P C I) c hx queries frame trace ok1 out1 ok2
 · exact NNE_EntryArgs.count _ 3 _ _
 · exact NNE_EntryArgs.count _ 7 _ _
 · exact out2
'''
p=Path('evidence/phys-adapter-20261111/NNE_PhysicalTop.lean')
p.write_text('import NNE_TopSplit\nset_option autoImplicit false\nnoncomputable section\nnamespace NNE_PhysicalTop\nopen RSL RSL.TAS RSL.TFM NNE_TopSplit\nopen RSL.TX2_241 (V2Lib)\nopen RSL.TX1_345 (S1Lib)\n'+t2+body+'\n#print axioms physical_top_split\nend NNE_PhysicalTop\nend\n')
