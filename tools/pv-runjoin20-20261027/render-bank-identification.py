from pathlib import Path
import sys
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
imports=['import R1Z.PV_RunJoin_SourceZero20','import R1Z.PV_RunJoin_SourceNode0420']+[f'import R1Z.PV_RunJoin_SourceNodes{x:02}20' for x in [5,9,13,17,21,54,34,38,42,46,50]]+[f'import R1Z.PV_RunJoin_SourceSponge{x:02}20' for x in [0,1,2,3,25,26,27,28,29,30,31,32]]
s='\n'.join(imports)+'''\nset_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BankIdentification20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1 BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_Src_ExternalReference.dictionary
'''
for kind,wd in [('transfer','false'),('withdrawal','true')]:
 s+=f'''theorem {kind}_blocks (pt : Parts) (hp : parts {kind}Witness {kind}Public = ok pt) :
    ∀ b, b < 57 → ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[b]!).val[row*16+lane]! =
        ((PV_RunJoin_FixtureBanks19.certificate {wd} b).row row).val[lane]! := by
  intro b hb
  interval_cases b
'''
 for b in range(57):
  if kind=='withdrawal' and b in [27,28,29]:name=f'PV_RunJoin_SourceZero20.block{b}'
  elif b in list(range(4))+[25,26,27,28,29,30,31,32]:name=f'PV_RunJoin_SourceSponge{b:02}20.{kind}.rows'
  else:name=f'PV_RunJoin_SourceNode{b:02}20.{kind}.rows'
  s+=f'  · exact {name} pt hp\n'
 s+=f'#print axioms {kind}_blocks\n'
 s+=f'''theorem {kind} : pair_forest_trace.validate_forest_poseidon_rows PV_RunJoin_SourceBanks19.{kind}Bank = ok (.Ok ()) := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.{kind}
  exact PV_RunJoin_SourceBankValidation19.{kind} pt hp (PV_RunJoin_PartsCells19.tail pt)
    (PV_RunJoin_PartsCells19.cells pt {wd} ({kind}_blocks pt hp))
#print axioms {kind}
'''
s+='end R1Z.PV_RunJoin_BankIdentification20\n';p=L/'PV_RunJoin_BankIdentification20.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('57 named source/certificate block identifications per fixture -> actual bank validator')
