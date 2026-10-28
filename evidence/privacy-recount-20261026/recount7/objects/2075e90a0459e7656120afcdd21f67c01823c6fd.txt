import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes4620
import R1Z.PV_RunJoin_CopyGroup5420
import R1Z.PV_RunJoin_CopyGroup7220
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode5020.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5719.certificate
def left : Array U32 8#usize := Array.make 8#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,1572976171#u32,358772057#u32,1351134296#u32]
def right : Array U32 8#usize := Array.make 8#usize [1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,2083375353#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change 2147483647 ≤ 2083375353 + 1095962629
        norm_num
      rw [if_pos guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5720.canon PV_RunJoin_CopyCell5720.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 16 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4920.transfer.c.states 11)) := PV_RunJoin_SourceNode4920.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[16]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨16,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[16]! = PV_RunJoin_RootModel.literal ⟨16,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨16,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨16,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨16,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4920.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 16) (appBitR (wordPublic transferPublic) 16) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4920.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[16]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 50 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 16) zero8) (appSibR (wordPublic transferPublic) 16) (appBitR (wordPublic transferPublic) 16) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 17 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 16
    let o := orderedR cur (appSibR (wordPublic transferPublic) 16) (appBitR (wordPublic transferPublic) 16)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 50 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 50 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 50).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 50).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5720.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[50]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 50 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5020.transfer
namespace R1Z.PV_RunJoin_SourceNode5020.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7719.certificate
def left : Array U32 8#usize := Array.make 8#usize [475693174#u32,322457381#u32,396535705#u32,1030492646#u32,176446941#u32,912396166#u32,1443369366#u32,2063088540#u32]
def right : Array U32 8#usize := Array.make 8#usize [1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,2083375353#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change 2147483647 ≤ 2083375353 + 1095962629
        norm_num
      rw [if_pos guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7720.canon PV_RunJoin_CopyCell7720.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4920.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4920.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[16]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨16,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[16]! = PV_RunJoin_RootModel.literal ⟨16,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨16,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨16,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨16,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4920.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 16) (appBitR (wordPublic withdrawalPublic) 16) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4920.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[16]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 50 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16) zero8) (appSibR (wordPublic withdrawalPublic) 16) (appBitR (wordPublic withdrawalPublic) 16) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 16) (appBitR (wordPublic withdrawalPublic) 16)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 50 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 50 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 50).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 50).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7720.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[50]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 50 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5020.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode5120.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5819.certificate
def left : Array U32 8#usize := Array.make 8#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,1691775382#u32,1825776613#u32,369526834#u32,1655898863#u32]
def right : Array U32 8#usize := Array.make 8#usize [1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,1299980413#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change 2147483647 ≤ 1299980413 + 1095962629
        norm_num
      rw [if_pos guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5820.canon PV_RunJoin_CopyCell5820.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 17 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5020.transfer.c.states 11)) := PV_RunJoin_SourceNode5020.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[17]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨17,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[17]! = PV_RunJoin_RootModel.literal ⟨17,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨17,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨17,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨17,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5020.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 17) (appBitR (wordPublic transferPublic) 17) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5020.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[17]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 51 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 17) zero8) (appSibR (wordPublic transferPublic) 17) (appBitR (wordPublic transferPublic) 17) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 18 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 17
    let o := orderedR cur (appSibR (wordPublic transferPublic) 17) (appBitR (wordPublic transferPublic) 17)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 51 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 51 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 51).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 51).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5820.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[51]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 51 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5120.transfer
namespace R1Z.PV_RunJoin_SourceNode5120.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7819.certificate
def left : Array U32 8#usize := Array.make 8#usize [223002281#u32,116293184#u32,1618212914#u32,1331700281#u32,2109368512#u32,559795428#u32,204366681#u32,229282374#u32]
def right : Array U32 8#usize := Array.make 8#usize [1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,1299980413#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change 2147483647 ≤ 1299980413 + 1095962629
        norm_num
      rw [if_pos guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7820.canon PV_RunJoin_CopyCell7820.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5020.withdrawal.c.states 11)) := PV_RunJoin_SourceNode5020.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[17]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨17,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[17]! = PV_RunJoin_RootModel.literal ⟨17,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨17,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨17,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨17,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5020.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 17) (appBitR (wordPublic withdrawalPublic) 17) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5020.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[17]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 51 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17) zero8) (appSibR (wordPublic withdrawalPublic) 17) (appBitR (wordPublic withdrawalPublic) 17) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 17) (appBitR (wordPublic withdrawalPublic) 17)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 51 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 51 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 51).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 51).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7820.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[51]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 51 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5120.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode5220.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5919.certificate
def left : Array U32 8#usize := Array.make 8#usize [1660714618#u32,58624303#u32,617770228#u32,599383446#u32,771361068#u32,1834589194#u32,51322319#u32,276611708#u32]
def right : Array U32 8#usize := Array.make 8#usize [1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,450526803#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : ¬ 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change ¬ 2147483647 ≤ 450526803 + 1095962629
        norm_num
      rw [if_neg guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5920.canon PV_RunJoin_CopyCell5920.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 18 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5120.transfer.c.states 11)) := PV_RunJoin_SourceNode5120.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[18]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨18,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[18]! = PV_RunJoin_RootModel.literal ⟨18,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨18,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨18,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨18,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5120.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 18) (appBitR (wordPublic transferPublic) 18) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5120.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[18]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 52 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 18) zero8) (appSibR (wordPublic transferPublic) 18) (appBitR (wordPublic transferPublic) 18) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 19 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 18
    let o := orderedR cur (appSibR (wordPublic transferPublic) 18) (appBitR (wordPublic transferPublic) 18)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 52 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 52 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 52).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 52).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[52]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 52 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5220.transfer
namespace R1Z.PV_RunJoin_SourceNode5220.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7919.certificate
def left : Array U32 8#usize := Array.make 8#usize [204734161#u32,1001842950#u32,1957867491#u32,1426920886#u32,531978693#u32,466210636#u32,1100375901#u32,1136408495#u32]
def right : Array U32 8#usize := Array.make 8#usize [1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,450526803#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : ¬ 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change ¬ 2147483647 ≤ 450526803 + 1095962629
        norm_num
      rw [if_neg guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7920.canon PV_RunJoin_CopyCell7920.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5120.withdrawal.c.states 11)) := PV_RunJoin_SourceNode5120.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[18]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨18,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[18]! = PV_RunJoin_RootModel.literal ⟨18,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨18,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨18,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨18,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5120.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 18) (appBitR (wordPublic withdrawalPublic) 18) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5120.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[18]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 52 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18) zero8) (appSibR (wordPublic withdrawalPublic) 18) (appBitR (wordPublic withdrawalPublic) 18) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 18) (appBitR (wordPublic withdrawalPublic) 18)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 52 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 52 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 52).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 52).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[52]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 52 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5220.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode5320.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell6019.certificate
def left : Array U32 8#usize := Array.make 8#usize [1186265903#u32,415151008#u32,1902434632#u32,1450931092#u32,922955725#u32,1977809658#u32,160284130#u32,1987330095#u32]
def right : Array U32 8#usize := Array.make 8#usize [19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,665567443#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : ¬ 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change ¬ 2147483647 ≤ 665567443 + 1095962629
        norm_num
      rw [if_neg guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell6020.canon PV_RunJoin_CopyCell6020.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 19 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5220.transfer.c.states 11)) := PV_RunJoin_SourceNode5220.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[19]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨19,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[19]! = PV_RunJoin_RootModel.literal ⟨19,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨19,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨19,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨19,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5220.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 19) (appBitR (wordPublic transferPublic) 19) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5220.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[19]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 53 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 19) zero8) (appSibR (wordPublic transferPublic) 19) (appBitR (wordPublic transferPublic) 19) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 20 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 19
    let o := orderedR cur (appSibR (wordPublic transferPublic) 19) (appBitR (wordPublic transferPublic) 19)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 53 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 53 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 53).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 53).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell6020.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[53]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 53 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5320.transfer
namespace R1Z.PV_RunJoin_SourceNode5320.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell8019.certificate
def left : Array U32 8#usize := Array.make 8#usize [1898472488#u32,597255419#u32,137386091#u32,1805069421#u32,1817944500#u32,96708207#u32,529143660#u32,294781830#u32]
def right : Array U32 8#usize := Array.make 8#usize [19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,665567443#u32]

theorem pre : R0BlockCopies.node_pre right = ok c.pre := by
  apply PV_RunJoin_NodeShape20.pre
  · intro lane hl
    interval_cases lane <;> decide
  · intro lane hl
    interval_cases lane
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [show ¬ (15:Nat) < 8 by decide,show (15:Nat) = 15 by rfl,if_false,if_true]
      have guard : ¬ 2147483647 ≤ (right.val[7]!).val + 1095962629 := by
        change ¬ 2147483647 ≤ 665567443 + 1095962629
        norm_num
      rw [if_neg guard]
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell8020.canon PV_RunJoin_CopyCell8020.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5220.withdrawal.c.states 11)) := PV_RunJoin_SourceNode5220.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[19]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨19,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[19]! = PV_RunJoin_RootModel.literal ⟨19,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨19,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨19,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨19,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5220.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 19) (appBitR (wordPublic withdrawalPublic) 19) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5220.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[19]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 53 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19) zero8) (appSibR (wordPublic withdrawalPublic) 19) (appBitR (wordPublic withdrawalPublic) 19) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 19) (appBitR (wordPublic withdrawalPublic) 19)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 53 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 53 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 53).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 53).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell8020.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[53]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 53 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5320.withdrawal
