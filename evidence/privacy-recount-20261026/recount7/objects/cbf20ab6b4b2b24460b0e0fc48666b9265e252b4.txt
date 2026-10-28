import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes5420
import R1Z.PV_RunJoin_CopyGroup3620
import R1Z.PV_RunJoin_CopyGroup5420
import R1Z.PV_RunJoin_CopyGroup6320
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode3420.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell4119.certificate
def left : Array U32 8#usize := Array.make 8#usize [1134794151#u32,415789335#u32,111944968#u32,1818281472#u32,628958070#u32,505282998#u32,905808425#u32,2134856457#u32]
def right : Array U32 8#usize := Array.make 8#usize [1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,1155026732#u32]

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
        change 2147483647 ≤ 1155026732 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell4120.canon PV_RunJoin_CopyCell4120.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 0 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3320.transfer.c.states 11)) := PV_RunJoin_SourceNode3320.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[0]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨0,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[0]! = PV_RunJoin_RootModel.literal ⟨0,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨0,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨0,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨0,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3320.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 0) (appBitR (wordPublic transferPublic) 0) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3320.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[0]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 34 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 0) zero8) (appSibR (wordPublic transferPublic) 0) (appBitR (wordPublic transferPublic) 0) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 1 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 0
    let o := orderedR cur (appSibR (wordPublic transferPublic) 0) (appBitR (wordPublic transferPublic) 0)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 34 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 34 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 34).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 34).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell4120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[34]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 34 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3420.transfer
namespace R1Z.PV_RunJoin_SourceNode3420.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell6119.certificate
def left : Array U32 8#usize := Array.make 8#usize [1635444076#u32,565453809#u32,2007649881#u32,905247732#u32,1187015924#u32,827186728#u32,137720039#u32,588419202#u32]
def right : Array U32 8#usize := Array.make 8#usize [1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,1155026732#u32]

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
        change 2147483647 ≤ 1155026732 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell6120.canon PV_RunJoin_CopyCell6120.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 0 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3320.withdrawal.c.states 11)) := PV_RunJoin_SourceNode3320.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[0]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨0,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[0]! = PV_RunJoin_RootModel.literal ⟨0,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨0,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨0,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨0,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3320.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 0) (appBitR (wordPublic withdrawalPublic) 0) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3320.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[0]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 34 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 0) zero8) (appSibR (wordPublic withdrawalPublic) 0) (appBitR (wordPublic withdrawalPublic) 0) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 1 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 0
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 0) (appBitR (wordPublic withdrawalPublic) 0)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 34 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 34 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 34).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 34).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell6120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[34]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 34 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3420.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode3520.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell4219.certificate
def left : Array U32 8#usize := Array.make 8#usize [1939205616#u32,641788683#u32,1281268521#u32,866499727#u32,385183050#u32,1408789791#u32,1189739305#u32,569851020#u32]
def right : Array U32 8#usize := Array.make 8#usize [141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,1038346536#u32]

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
        change ¬ 2147483647 ≤ 1038346536 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell4220.canon PV_RunJoin_CopyCell4220.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 1 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3420.transfer.c.states 11)) := PV_RunJoin_SourceNode3420.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[1]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨1,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[1]! = PV_RunJoin_RootModel.literal ⟨1,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨1,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨1,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨1,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3420.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 1) (appBitR (wordPublic transferPublic) 1) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3420.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[1]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 35 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 1) zero8) (appSibR (wordPublic transferPublic) 1) (appBitR (wordPublic transferPublic) 1) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 2 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 1
    let o := orderedR cur (appSibR (wordPublic transferPublic) 1) (appBitR (wordPublic transferPublic) 1)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 35 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 35 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 35).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 35).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell4220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[35]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 35 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3520.transfer
namespace R1Z.PV_RunJoin_SourceNode3520.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell6219.certificate
def left : Array U32 8#usize := Array.make 8#usize [609870583#u32,958510084#u32,2094278047#u32,743619649#u32,1992887085#u32,2048705761#u32,118223484#u32,1828066596#u32]
def right : Array U32 8#usize := Array.make 8#usize [141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,1038346536#u32]

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
        change ¬ 2147483647 ≤ 1038346536 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell6220.canon PV_RunJoin_CopyCell6220.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 1 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3420.withdrawal.c.states 11)) := PV_RunJoin_SourceNode3420.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[1]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨1,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[1]! = PV_RunJoin_RootModel.literal ⟨1,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨1,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨1,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨1,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3420.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 1) (appBitR (wordPublic withdrawalPublic) 1) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3420.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[1]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 35 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 1) zero8) (appSibR (wordPublic withdrawalPublic) 1) (appBitR (wordPublic withdrawalPublic) 1) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 2 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 1
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 1) (appBitR (wordPublic withdrawalPublic) 1)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 35 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 35 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 35).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 35).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell6220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[35]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 35 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3520.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode3620.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell4319.certificate
def left : Array U32 8#usize := Array.make 8#usize [1133998657#u32,190536997#u32,632216762#u32,2145002820#u32,1218690534#u32,1341831920#u32,1813986794#u32,962659369#u32]
def right : Array U32 8#usize := Array.make 8#usize [1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,1398246146#u32]

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
        change 2147483647 ≤ 1398246146 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell4320.canon PV_RunJoin_CopyCell4320.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 2 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3520.transfer.c.states 11)) := PV_RunJoin_SourceNode3520.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[2]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨2,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[2]! = PV_RunJoin_RootModel.literal ⟨2,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨2,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨2,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨2,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3520.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 2) (appBitR (wordPublic transferPublic) 2) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3520.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[2]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 36 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 2) zero8) (appSibR (wordPublic transferPublic) 2) (appBitR (wordPublic transferPublic) 2) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 3 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 2
    let o := orderedR cur (appSibR (wordPublic transferPublic) 2) (appBitR (wordPublic transferPublic) 2)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 36 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 36 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 36).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 36).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell4320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[36]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 36 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3620.transfer
namespace R1Z.PV_RunJoin_SourceNode3620.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell6319.certificate
def left : Array U32 8#usize := Array.make 8#usize [1640108137#u32,330515254#u32,212366917#u32,1785570475#u32,1241175939#u32,132178283#u32,1767391975#u32,136033189#u32]
def right : Array U32 8#usize := Array.make 8#usize [1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,1398246146#u32]

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
        change 2147483647 ≤ 1398246146 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell6320.canon PV_RunJoin_CopyCell6320.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 2 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3520.withdrawal.c.states 11)) := PV_RunJoin_SourceNode3520.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[2]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨2,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[2]! = PV_RunJoin_RootModel.literal ⟨2,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨2,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨2,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨2,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3520.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 2) (appBitR (wordPublic withdrawalPublic) 2) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3520.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[2]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 36 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 2) zero8) (appSibR (wordPublic withdrawalPublic) 2) (appBitR (wordPublic withdrawalPublic) 2) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 3 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 2
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 2) (appBitR (wordPublic withdrawalPublic) 2)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 36 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 36 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 36).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 36).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell6320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[36]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 36 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3620.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode3720.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell4419.certificate
def left : Array U32 8#usize := Array.make 8#usize [1061398933#u32,509112012#u32,1799578086#u32,482877258#u32,2025164722#u32,672733548#u32,359961336#u32,1470147015#u32]
def right : Array U32 8#usize := Array.make 8#usize [1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,2024887573#u32]

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
        change 2147483647 ≤ 2024887573 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell4420.canon PV_RunJoin_CopyCell4420.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 3 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3620.transfer.c.states 11)) := PV_RunJoin_SourceNode3620.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[3]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨3,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[3]! = PV_RunJoin_RootModel.literal ⟨3,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨3,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨3,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨3,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3620.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 3) (appBitR (wordPublic transferPublic) 3) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3620.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[3]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 37 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 3) zero8) (appSibR (wordPublic transferPublic) 3) (appBitR (wordPublic transferPublic) 3) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 4 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 3
    let o := orderedR cur (appSibR (wordPublic transferPublic) 3) (appBitR (wordPublic transferPublic) 3)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 37 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 37 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 37).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 37).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell4420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[37]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 37 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3720.transfer
namespace R1Z.PV_RunJoin_SourceNode3720.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell6419.certificate
def left : Array U32 8#usize := Array.make 8#usize [432585881#u32,1344347431#u32,436199667#u32,1321219941#u32,1344313237#u32,719981873#u32,669780265#u32,1723074008#u32]
def right : Array U32 8#usize := Array.make 8#usize [1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,2024887573#u32]

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
        change 2147483647 ≤ 2024887573 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell6420.canon PV_RunJoin_CopyCell6420.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 3 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3620.withdrawal.c.states 11)) := PV_RunJoin_SourceNode3620.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[3]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨3,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[3]! = PV_RunJoin_RootModel.literal ⟨3,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨3,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨3,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨3,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3620.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 3) (appBitR (wordPublic withdrawalPublic) 3) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode3620.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[3]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 37 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 3) zero8) (appSibR (wordPublic withdrawalPublic) 3) (appBitR (wordPublic withdrawalPublic) 3) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 4 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 3
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 3) (appBitR (wordPublic withdrawalPublic) 3)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 37 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 37 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 37).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 37).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell6420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[37]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 37 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3720.withdrawal
