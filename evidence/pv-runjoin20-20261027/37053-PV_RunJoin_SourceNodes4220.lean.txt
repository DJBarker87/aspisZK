import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes3820
import R1Z.PV_RunJoin_CopyGroup4520
import R1Z.PV_RunJoin_CopyGroup6320
import R1Z.PV_RunJoin_CopyGroup7220
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4220.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell4919.certificate
def left : Array U32 8#usize := Array.make 8#usize [985515685#u32,670227816#u32,320139735#u32,164221359#u32,586867065#u32,504851391#u32,659699442#u32,1594817757#u32]
def right : Array U32 8#usize := Array.make 8#usize [27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,553704718#u32]

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
        change ¬ 2147483647 ≤ 553704718 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell4920.canon PV_RunJoin_CopyCell4920.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 8 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4120.transfer.c.states 11)) := PV_RunJoin_SourceNode4120.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[8]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨8,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[8]! = PV_RunJoin_RootModel.literal ⟨8,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨8,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨8,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨8,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4120.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 8) (appBitR (wordPublic transferPublic) 8) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4120.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[8]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 42 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 8) zero8) (appSibR (wordPublic transferPublic) 8) (appBitR (wordPublic transferPublic) 8) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 9 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 8
    let o := orderedR cur (appSibR (wordPublic transferPublic) 8) (appBitR (wordPublic transferPublic) 8)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 42 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 42 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 42).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 42).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell4920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[42]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 42 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4220.transfer
namespace R1Z.PV_RunJoin_SourceNode4220.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell6919.certificate
def left : Array U32 8#usize := Array.make 8#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,10140345#u32,2116907504#u32,1823343454#u32]
def right : Array U32 8#usize := Array.make 8#usize [27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,553704718#u32]

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
        change ¬ 2147483647 ≤ 553704718 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell6920.canon PV_RunJoin_CopyCell6920.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 8 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4120.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4120.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[8]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨8,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[8]! = PV_RunJoin_RootModel.literal ⟨8,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨8,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨8,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨8,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4120.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 8) (appBitR (wordPublic withdrawalPublic) 8) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4120.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[8]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 42 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 8) zero8) (appSibR (wordPublic withdrawalPublic) 8) (appBitR (wordPublic withdrawalPublic) 8) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 8
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 8) (appBitR (wordPublic withdrawalPublic) 8)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 42 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 42 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 42).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 42).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell6920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[42]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 42 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4220.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4320.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5019.certificate
def left : Array U32 8#usize := Array.make 8#usize [210048012#u32,966687588#u32,869731705#u32,823470673#u32,703197799#u32,1759368079#u32,456367603#u32,772376783#u32]
def right : Array U32 8#usize := Array.make 8#usize [1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,1653526885#u32]

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
        change 2147483647 ≤ 1653526885 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5020.canon PV_RunJoin_CopyCell5020.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 9 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4220.transfer.c.states 11)) := PV_RunJoin_SourceNode4220.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[9]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨9,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[9]! = PV_RunJoin_RootModel.literal ⟨9,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨9,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨9,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨9,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4220.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 9) (appBitR (wordPublic transferPublic) 9) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4220.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[9]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 43 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 9) zero8) (appSibR (wordPublic transferPublic) 9) (appBitR (wordPublic transferPublic) 9) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 10 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 9
    let o := orderedR cur (appSibR (wordPublic transferPublic) 9) (appBitR (wordPublic transferPublic) 9)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 43 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 43 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 43).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 43).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5020.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[43]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 43 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4320.transfer
namespace R1Z.PV_RunJoin_SourceNode4320.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7019.certificate
def left : Array U32 8#usize := Array.make 8#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,81172068#u32,361707637#u32,1111542572#u32]
def right : Array U32 8#usize := Array.make 8#usize [1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,1653526885#u32]

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
        change 2147483647 ≤ 1653526885 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7020.canon PV_RunJoin_CopyCell7020.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4220.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4220.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[9]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨9,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[9]! = PV_RunJoin_RootModel.literal ⟨9,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨9,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨9,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨9,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4220.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 9) (appBitR (wordPublic withdrawalPublic) 9) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4220.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[9]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 43 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9) zero8) (appSibR (wordPublic withdrawalPublic) 9) (appBitR (wordPublic withdrawalPublic) 9) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 9) (appBitR (wordPublic withdrawalPublic) 9)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 43 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 43 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 43).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 43).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7020.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[43]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 43 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4320.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4420.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5119.certificate
def left : Array U32 8#usize := Array.make 8#usize [1483663627#u32,500119681#u32,2118402728#u32,174107570#u32,654106964#u32,85317403#u32,1579623758#u32,1770549948#u32]
def right : Array U32 8#usize := Array.make 8#usize [418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,1800828893#u32]

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
        change 2147483647 ≤ 1800828893 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5120.canon PV_RunJoin_CopyCell5120.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 10 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4320.transfer.c.states 11)) := PV_RunJoin_SourceNode4320.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[10]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨10,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[10]! = PV_RunJoin_RootModel.literal ⟨10,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨10,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨10,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨10,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4320.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 10) (appBitR (wordPublic transferPublic) 10) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4320.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[10]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 44 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 10) zero8) (appSibR (wordPublic transferPublic) 10) (appBitR (wordPublic transferPublic) 10) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 11 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 10
    let o := orderedR cur (appSibR (wordPublic transferPublic) 10) (appBitR (wordPublic transferPublic) 10)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 44 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 44 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 44).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 44).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[44]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 44 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4420.transfer
namespace R1Z.PV_RunJoin_SourceNode4420.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7119.certificate
def left : Array U32 8#usize := Array.make 8#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,1075792838#u32,352883826#u32,459345458#u32]
def right : Array U32 8#usize := Array.make 8#usize [418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,1800828893#u32]

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
        change 2147483647 ≤ 1800828893 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7120.canon PV_RunJoin_CopyCell7120.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4320.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4320.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[10]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨10,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[10]! = PV_RunJoin_RootModel.literal ⟨10,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨10,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨10,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨10,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4320.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 10) (appBitR (wordPublic withdrawalPublic) 10) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4320.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[10]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 44 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10) zero8) (appSibR (wordPublic withdrawalPublic) 10) (appBitR (wordPublic withdrawalPublic) 10) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 10) (appBitR (wordPublic withdrawalPublic) 10)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 44 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 44 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 44).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 44).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[44]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 44 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4420.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4520.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5219.certificate
def left : Array U32 8#usize := Array.make 8#usize [578338833#u32,1226544375#u32,1719735936#u32,2046596019#u32,1635531819#u32,454303639#u32,1556588950#u32,1520337232#u32]
def right : Array U32 8#usize := Array.make 8#usize [986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,1280042062#u32]

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
        change 2147483647 ≤ 1280042062 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5220.canon PV_RunJoin_CopyCell5220.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 11 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4420.transfer.c.states 11)) := PV_RunJoin_SourceNode4420.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[11]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨11,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[11]! = PV_RunJoin_RootModel.literal ⟨11,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨11,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨11,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨11,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4420.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 11) (appBitR (wordPublic transferPublic) 11) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4420.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[11]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 45 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 11) zero8) (appSibR (wordPublic transferPublic) 11) (appBitR (wordPublic transferPublic) 11) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 12 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 11
    let o := orderedR cur (appSibR (wordPublic transferPublic) 11) (appBitR (wordPublic transferPublic) 11)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 45 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 45 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 45).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 45).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[45]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 45 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4520.transfer
namespace R1Z.PV_RunJoin_SourceNode4520.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7219.certificate
def left : Array U32 8#usize := Array.make 8#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,982012671#u32,514446081#u32,115798455#u32]
def right : Array U32 8#usize := Array.make 8#usize [986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,1280042062#u32]

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
        change 2147483647 ≤ 1280042062 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7220.canon PV_RunJoin_CopyCell7220.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4420.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4420.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[11]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨11,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[11]! = PV_RunJoin_RootModel.literal ⟨11,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨11,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨11,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨11,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4420.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 11) (appBitR (wordPublic withdrawalPublic) 11) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4420.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[11]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 45 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11) zero8) (appSibR (wordPublic withdrawalPublic) 11) (appBitR (wordPublic withdrawalPublic) 11) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 11) (appBitR (wordPublic withdrawalPublic) 11)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 45 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 45 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 45).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 45).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[45]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 45 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4520.withdrawal
