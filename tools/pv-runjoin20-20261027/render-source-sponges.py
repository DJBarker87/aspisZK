from pathlib import Path
import sys
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
steps=[0,1,2,3,25,26,27,28,29,30,31,32]
base={0:0,1:1,2:1,3:1,25:25,26:25,27:27,28:27,29:27,30:30,31:30,32:30}
for h in steps:
 imports=['import R1Z.PV_RunJoin_AbsorbShape20','import R1Z.PV_RunJoin_CopyCell0020']+[f'import R1Z.PV_RunJoin_CopyGroup{g:02}20' for g in [0,27,36]]
 if h!=0:imports.append(f'import R1Z.PV_RunJoin_SourceSponge{(h-1 if h in [2,3,26,28,29,31,32] else 0):02}20')
 out='\n'.join(imports)+'\nset_option autoImplicit false\nnoncomputable section\n'
 for kind in ['transfer','withdrawal']:
  if kind=='withdrawal' and 27<=h<=29:continue
  j={0:0,1:1,2:2,3:3,25:4,26:5,27:30,28:31,29:32,30:33,31:34,32:35}[h]
  if kind=='withdrawal' and h>=30:j+=3
  ns=f'PV_RunJoin_SourceSponge{h:02}20.{kind}';prev=lambda k:f'PV_RunJoin_SourceSponge{k:02}20.{kind}'
  W=f'(wordWitness {kind}Witness)';P=f'(wordPublic {kind}Public)';R=f'(rustChunks {W} {P})';c=f'PV_RunJoin_BankCell{j:02}19.certificate';cell=f'PV_RunJoin_CopyCell{j:02}20'
  out+=f'''namespace R1Z.{ns}
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := {c}
'''
  if h==base[h]:
   init='initOwner' if h==0 else 'initNul' if h==25 else 'initNote'
   out+=f'''theorem init : {init} = ok c.pre := by with_unfolding_all rfl
#print axioms init
theorem pre : spongePre {R} {h} = ok c.pre := init
#print axioms pre
'''
  else:
   init='initNul' if h==26 else 'initNote';b=base[h]
   expr=f'''(do
    let p ← {init}
'''
   if h==b+2:expr+=f'    let p ← spongeStep p ({R}.schunk {b}) ({R}.sclen {b})\n'
   expr+=f'    spongeStep p ({R}.schunk {h-1}) ({R}.sclen {h-1}))'
   out+=f'''theorem pre : spongePre {R} {h} = ok c.pre := by
  change {expr} = _
  rw [{prev(b)}.init]
  simp only [bind_tc_ok]
'''
   if h==b+2:out+=f'  rw [{prev(b)}.step]\n  simp only [bind_tc_ok]\n'
   out+=f'  exact {prev(h-1)}.step\n#print axioms pre\n'
  out+=f'''theorem absorb : R0BlockCopies.sponge_absorb ({R}.schunk {h}) ({R}.sclen {h}) = ok c.absorption := by
'''
  if h==1:
   out+=f'''  change R0BlockCopies.sponge_absorb (okOr (ownerD {W}) zero8) 8#usize = _
  rw [{prev(0)}.owner,okOr_ok]
'''
  out+='''  apply PV_RunJoin_AbsorbShape20.sponge
  intro lane hl
  interval_cases lane <;> with_unfolding_all rfl
#print axioms absorb
'''
  out+=f'''theorem step : spongeStep c.pre ({R}.schunk {h}) ({R}.sclen {h}) = ok (c.states 11) :=
  PV_RunJoin_CertificateExecution20.sponge c {cell}.canon {cell}.models _ _ absorb
#print axioms step

theorem digest : spongeDigestR c.pre ({R}.schunk {h}) ({R}.sclen {h}) = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  rw [spongeDigestR,absorb]
  simp only [bind_tc_ok]
  exact PV_RunJoin_CertificateExecution20.digest c {cell}.canon {cell}.models
#print axioms digest
'''
  if h==0:
   out+=f'''theorem owner : ownerD {W} = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  rw [ownerD,init]
  simp only [bind_tc_ok]
  exact digest
#print axioms owner
'''
  out+=f'''theorem chain : ∃ block, RustWriterChain {P}.variant {R} {h} = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.sponge {kind}Witness {kind}Public {h} c
    (by decide) (by decide) pre absorb {cell}.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts {kind}Witness {kind}Public = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[{h}]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ {h} (by decide) c chain pt hp
#print axioms rows
end R1Z.{ns}
'''
 p=L/f'PV_RunJoin_SourceSponge{h:02}20.lean'
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
print('twelve source sponge blocks generated with named predecessor executions')
