from pathlib import Path
import json,re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
data={}
for fn in ['FixtureHashData','PathData16','OutputData16']:
 for m in re.finditer(r'def s_(\d+)_(\d+) .*? := !\[(.*?)\]',(L/f'PV_RunJoin_{fn}.lean').read_text()):data[int(m[1]),int(m[2])]=list(map(int,m[3].split(',')))
bs=(L/'PV_RunJoin_FixtureBanks19.lean').read_text();maps={}
for kind in ['transfer','withdrawal']:
 body=bs.split(f'def {kind}Certificate')[1].split('def ')[0];maps[kind]={int(a):int(b) for a,b in re.findall(r'\| (\d+) => PV_RunJoin_BankCell(\d+)19.certificate',body)}
steps=list(range(4,25))+[54,55,56,33]+list(range(34,54))
for h in steps:
 idx=steps.index(h);pred=steps[idx-1] if idx else None
 imports=['import R1Z.PV_RunJoin_NodeExecution20','import R1Z.PV_RunJoin_SourceSponge0320','import R1Z.PV_RunJoin_SourceSponge2920','import R1Z.PV_RunJoin_SourceSponge3220','import R1Z.PV_RunJoin_ZeroConstructor18']
 if pred is not None:imports.append(f'import R1Z.PV_RunJoin_SourceNode{pred:02}20')
 for g in sorted({(maps[k][h]//9)*9 for k in maps}):imports.append(f'import R1Z.PV_RunJoin_CopyGroup{g:02}20')
 out='\n'.join(imports)+'\nset_option autoImplicit false\nnoncomputable section\n'
 for kind in ['transfer','withdrawal']:
  j=maps[kind][h];c=f'PV_RunJoin_BankCell{j:02}19.certificate';copy=f'PV_RunJoin_CopyCell{j:02}20';ns=f'PV_RunJoin_SourceNode{h:02}20.{kind}'
  W=f'(wordWitness {kind}Witness)';P=f'(wordPublic {kind}Public)';chunks=f'(rustChunks {W} {P})'
  initial=data[j,0];left=initial[:8];right=initial[8:];right[-1]=(right[-1]-1095962629)%2147483647
  arr=lambda a:'Array.make 8#usize ['+','.join(f'{x}#u32' for x in a)+']'
  out+=f'''namespace R1Z.{ns}
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := {c}
def left : Array U32 8#usize := {arr(left)}
def right : Array U32 8#usize := {arr(right)}

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
{''.join('    · with_unfolding_all rfl'+chr(10) for _ in range(15))}    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : {'2147483647 ≤ (right.val[7]!).val + 1095962629' if right[7]+1095962629>=2147483647 else '¬ 2147483647 ≤ (right.val[7]!).val + 1095962629'} := by
        change {'2147483647 ≤ '+str(right[7])+' + 1095962629' if right[7]+1095962629>=2147483647 else '¬ 2147483647 ≤ '+str(right[7])+' + 1095962629'}
        norm_num
      rw [{'if_pos' if right[7]+1095962629>=2147483647 else 'if_neg'} guard]
      with_unfolding_all rfl
#print axioms pre

theorem absorb : R0BlockCopies.node_absorb left = ok c.absorption := by
  apply PV_RunJoin_NodeShape20.absorb
  intro lane hl
  interval_cases lane <;> with_unfolding_all rfl
#print axioms absorb

theorem node : nodeDigestR left right = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  rw [nodeDigestR,pre]
  simp only [bind_tc_ok]
  rw [absorb]
  simp only [bind_tc_ok]
  exact PV_RunJoin_CertificateExecution20.digest c {copy}.canon {copy}.models
#print axioms node
'''
  # base note digest laws
  if h in [4,33]:
   notes=[('leaf',3,'inputLeafR')] if h==4 else ([('recipient',29,'recipDR'),('change',32,'changeDR')] if kind=='transfer' else [('change',32,'changeDR')])
   for label,nh,fn in notes:
    src=f'PV_RunJoin_SourceSponge{nh:02}20.{kind}'
    out+=f'''theorem {label} : {fn} {W} {P} = ok (R0Z.WriterRefine.digest8 ({src}.c.states 11)) := by
  rw [{fn},noteDigestR]
  change (do
    let p ← spongePre {chunks} {nh}
    spongeDigestR p ({chunks}.schunk {nh}) ({chunks}.sclen {nh})) = _
  rw [{src}.pre]
  simp only [bind_tc_ok]
  exact {src}.digest
#print axioms {label}
'''
  if h==33:
   srcR=f'PV_RunJoin_SourceSponge2920.{kind}';srcC=f'PV_RunJoin_SourceSponge3220.{kind}'
   if kind=='transfer':out+=f'''theorem children : childrenOf {W} {P} 33 = (left,right) := by
  change (okOr (recipDR {W} {P}) zero8,okOr (changeDR {W} {P}) zero8) = _
  rw [recipient,change,okOr_ok,okOr_ok]
  with_unfolding_all rfl
#print axioms children

theorem next : outPairR {W} {P} = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let r ← recipDR {W} {P}
    let c ← changeDR {W} {P}
    nodeDigestR r c) = _
  rw [recipient]
  simp only [bind_tc_ok]
  rw [change]
  simp only [bind_tc_ok]
  exact node
#print axioms next
'''
   else:out+=f'''theorem children : childrenOf {W} {P} 33 = (left,right) := by
  change (okOr (changeDR {W} {P}) zero8,zero8) = _
  rw [change,okOr_ok]
  with_unfolding_all rfl
#print axioms children

theorem next : outPairR {W} {P} = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let c ← changeDR {W} {P}
    nodeDigestR c zero8) = _
  rw [change]
  simp only [bind_tc_ok]
  exact node
#print axioms next
'''
  else:
   isapp=34<=h<=53;n=h-34 if isapp else h-4 if h<25 else h-33
   cursor='appCurR' if isapp else 'treeCurR';pns=f'PV_RunJoin_SourceNode{(h-1 if h!=54 else 24):02}20.{kind}'
   pc=f'{pns}.c' if n else ('PV_RunJoin_SourceNode3320.'+kind+'.c' if isapp else 'PV_RunJoin_SourceSponge0320.'+kind+'.c')
   dig=f'R0Z.WriterRefine.digest8 ({pc}.states 11)'
   if isapp and n==0:cursorproof=f'PV_RunJoin_SourceNode3320.{kind}.next'
   elif not isapp and n==0:cursorproof='leaf'
   else:cursorproof=f'{pns}.next'
   out+=f'''theorem cursor : {cursor} {W} {P} {n} = ok ({dig}) := {cursorproof}
#print axioms cursor
'''
   if isapp:
    out+=f'''theorem empty : PV_Src_CanonicalRoots.table.val[{n}]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨{n},by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[{n}]! = PV_RunJoin_RootModel.literal ⟨{n},by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨{n},by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨{n},by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨{n},by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
'''
   sib=f'(appSibR {P} {n})' if isapp else f'({W}.sibs.val[{n}]!)';bit=f'(appBitR {P} {n})' if isapp else f'(bitB {W} {n})'
   out+=f'''theorem ordered : orderedR ({dig}) {sib} {bit} = (left,right) := by
'''
   if isapp:out+=f'''  change ({dig},PV_Src_CanonicalRoots.table.val[{n}]!) = _
  rw [empty]
'''
   out+=f'''  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf {W} {P} {h} = (left,right) := by
  change orderedR (okOr ({cursor} {W} {P} {n}) zero8) {sib} {bit} = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : {cursor} {W} {P} {n+1} = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← {cursor} {W} {P} {n}
    let o := orderedR cur {sib} {bit}
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
'''
  out+=f'''theorem chain : ∃ block, RustWriterChain {P}.variant {chunks} {h} = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain {kind}Witness {kind}Public {h} c (by decide)
  · change R0BlockCopies.node_pre (childrenOf {W} {P} {h}).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf {W} {P} {h}).1 = _
    rw [children]
    exact absorb
  · exact {copy}.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts {kind}Witness {kind}Public = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[{h}]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ {h} (by decide) c chain pt hp
#print axioms rows
end R1Z.{ns}
'''
 p=L/f'PV_RunJoin_SourceNode{h:02}20.lean' if h==4 else R/'evidence/pv-runjoin20-20261027/node-drafts'/f'PV_RunJoin_SourceNode{h:02}20.lean.txt'
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
print('45 node blocks, named exact source cursor and children equations, both fixtures')
