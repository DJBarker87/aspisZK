import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes4220
import R1Z.PV_RunJoin_CopyGroup4520
import R1Z.PV_RunJoin_CopyGroup7220
import R1Z.PV_RunJoin_CopyGroup5420
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4620.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5319.certificate
def left : Array U32 8#usize := Array.make 8#usize [1033316416#u32,1871077402#u32,1557962334#u32,322514877#u32,1982083472#u32,813203847#u32,1866642001#u32,508617919#u32]
def right : Array U32 8#usize := Array.make 8#usize [2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,2053396184#u32]

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
        change 2147483647 ≤ 2053396184 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5320.canon PV_RunJoin_CopyCell5320.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 12 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4520.transfer.c.states 11)) := PV_RunJoin_SourceNode4520.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[12]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨12,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[12]! = PV_RunJoin_RootModel.literal ⟨12,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨12,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨12,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨12,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4520.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 12) (appBitR (wordPublic transferPublic) 12) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4520.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[12]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 46 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 12) zero8) (appSibR (wordPublic transferPublic) 12) (appBitR (wordPublic transferPublic) 12) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 13 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 12
    let o := orderedR cur (appSibR (wordPublic transferPublic) 12) (appBitR (wordPublic transferPublic) 12)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 46 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 46 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 46).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 46).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[46]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 46 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4620.transfer
namespace R1Z.PV_RunJoin_SourceNode4620.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7319.certificate
def left : Array U32 8#usize := Array.make 8#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,1511331359#u32,351180429#u32,2094192877#u32,1421708941#u32]
def right : Array U32 8#usize := Array.make 8#usize [2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,2053396184#u32]

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
        change 2147483647 ≤ 2053396184 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7320.canon PV_RunJoin_CopyCell7320.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4520.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4520.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[12]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨12,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[12]! = PV_RunJoin_RootModel.literal ⟨12,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨12,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨12,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨12,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4520.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 12) (appBitR (wordPublic withdrawalPublic) 12) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4520.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[12]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 46 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12) zero8) (appSibR (wordPublic withdrawalPublic) 12) (appBitR (wordPublic withdrawalPublic) 12) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 12) (appBitR (wordPublic withdrawalPublic) 12)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 46 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 46 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 46).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 46).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[46]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 46 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4620.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4720.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5419.certificate
def left : Array U32 8#usize := Array.make 8#usize [1310587138#u32,1547028228#u32,724201667#u32,460418645#u32,1935078033#u32,56710135#u32,329156384#u32,480377036#u32]
def right : Array U32 8#usize := Array.make 8#usize [260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,958210542#u32]

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
        change ¬ 2147483647 ≤ 958210542 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5420.canon PV_RunJoin_CopyCell5420.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 13 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4620.transfer.c.states 11)) := PV_RunJoin_SourceNode4620.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[13]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨13,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[13]! = PV_RunJoin_RootModel.literal ⟨13,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨13,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨13,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨13,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4620.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 13) (appBitR (wordPublic transferPublic) 13) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4620.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[13]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 47 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 13) zero8) (appSibR (wordPublic transferPublic) 13) (appBitR (wordPublic transferPublic) 13) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 14 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 13
    let o := orderedR cur (appSibR (wordPublic transferPublic) 13) (appBitR (wordPublic transferPublic) 13)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 47 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 47 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 47).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 47).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[47]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 47 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4720.transfer
namespace R1Z.PV_RunJoin_SourceNode4720.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7419.certificate
def left : Array U32 8#usize := Array.make 8#usize [1024910236#u32,34897137#u32,119525087#u32,2069845639#u32,34881120#u32,1632903117#u32,1891593814#u32,1830035060#u32]
def right : Array U32 8#usize := Array.make 8#usize [260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,958210542#u32]

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
        change ¬ 2147483647 ≤ 958210542 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7420.canon PV_RunJoin_CopyCell7420.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4620.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4620.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[13]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨13,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[13]! = PV_RunJoin_RootModel.literal ⟨13,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨13,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨13,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨13,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4620.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 13) (appBitR (wordPublic withdrawalPublic) 13) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4620.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[13]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 47 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13) zero8) (appSibR (wordPublic withdrawalPublic) 13) (appBitR (wordPublic withdrawalPublic) 13) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 13) (appBitR (wordPublic withdrawalPublic) 13)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 47 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 47 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 47).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 47).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[47]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 47 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4720.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4820.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5519.certificate
def left : Array U32 8#usize := Array.make 8#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,934340682#u32,707737539#u32,1640113194#u32,1531834504#u32]
def right : Array U32 8#usize := Array.make 8#usize [1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,1680224983#u32]

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
        change 2147483647 ≤ 1680224983 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5520.canon PV_RunJoin_CopyCell5520.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 14 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4720.transfer.c.states 11)) := PV_RunJoin_SourceNode4720.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[14]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨14,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[14]! = PV_RunJoin_RootModel.literal ⟨14,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨14,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨14,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨14,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4720.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 14) (appBitR (wordPublic transferPublic) 14) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4720.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[14]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 48 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 14) zero8) (appSibR (wordPublic transferPublic) 14) (appBitR (wordPublic transferPublic) 14) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 15 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 14
    let o := orderedR cur (appSibR (wordPublic transferPublic) 14) (appBitR (wordPublic transferPublic) 14)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 48 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 48 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 48).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 48).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5520.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[48]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 48 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4820.transfer
namespace R1Z.PV_RunJoin_SourceNode4820.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7519.certificate
def left : Array U32 8#usize := Array.make 8#usize [1669216135#u32,741703000#u32,562283949#u32,1060793623#u32,1378667390#u32,256051405#u32,1303928677#u32,1488857718#u32]
def right : Array U32 8#usize := Array.make 8#usize [1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,1680224983#u32]

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
        change 2147483647 ≤ 1680224983 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7520.canon PV_RunJoin_CopyCell7520.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4720.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4720.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[14]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨14,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[14]! = PV_RunJoin_RootModel.literal ⟨14,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨14,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨14,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨14,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4720.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 14) (appBitR (wordPublic withdrawalPublic) 14) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4720.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[14]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 48 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14) zero8) (appSibR (wordPublic withdrawalPublic) 14) (appBitR (wordPublic withdrawalPublic) 14) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 14) (appBitR (wordPublic withdrawalPublic) 14)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 48 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 48 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 48).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 48).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7520.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[48]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 48 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4820.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode4920.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell5619.certificate
def left : Array U32 8#usize := Array.make 8#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,2019127874#u32,1644297524#u32,121114825#u32]
def right : Array U32 8#usize := Array.make 8#usize [1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,1214723477#u32]

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
        change 2147483647 ≤ 1214723477 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell5620.canon PV_RunJoin_CopyCell5620.models
#print axioms node
theorem cursor : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 15 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4820.transfer.c.states 11)) := PV_RunJoin_SourceNode4820.transfer.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[15]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨15,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[15]! = PV_RunJoin_RootModel.literal ⟨15,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨15,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨15,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨15,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4820.transfer.c.states 11)) (appSibR (wordPublic transferPublic) 15) (appBitR (wordPublic transferPublic) 15) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4820.transfer.c.states 11),PV_Src_CanonicalRoots.table.val[15]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 49 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness transferWitness) (wordPublic transferPublic) 15) zero8) (appSibR (wordPublic transferPublic) 15) (appBitR (wordPublic transferPublic) 15) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness transferWitness) (wordPublic transferPublic) 16 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness transferWitness) (wordPublic transferPublic) 15
    let o := orderedR cur (appSibR (wordPublic transferPublic) 15) (appBitR (wordPublic transferPublic) 15)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 49 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 49 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 49).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 49).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell5620.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[49]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 49 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4920.transfer
namespace R1Z.PV_RunJoin_SourceNode4920.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell7619.certificate
def left : Array U32 8#usize := Array.make 8#usize [1385985564#u32,1312452205#u32,34748210#u32,2022077470#u32,1837706654#u32,827038403#u32,1892640303#u32,370983584#u32]
def right : Array U32 8#usize := Array.make 8#usize [1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,1214723477#u32]

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
        change 2147483647 ≤ 1214723477 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell7620.canon PV_RunJoin_CopyCell7620.models
#print axioms node
theorem cursor : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4820.withdrawal.c.states 11)) := PV_RunJoin_SourceNode4820.withdrawal.next
#print axioms cursor
theorem empty : PV_Src_CanonicalRoots.table.val[15]! = right := by
  apply PV_RunJoin_TreeValue16.unique
  · exact PV_Src_CanonicalRoots.canonical ⟨15,by decide⟩
  · intro lane hl
    interval_cases lane <;> decide
  · have he : digK (K := PV_RunJoin_FixtureRecords.M) PV_Src_CanonicalRoots.table.val[15]! = PV_RunJoin_RootModel.literal ⟨15,by decide⟩ := by
      with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨15,by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨15,by decide⟩))
    have ht : digK (K := PV_RunJoin_FixtureRecords.M) right = PV_RunJoin_RootModel.literal ⟨15,by decide⟩ := by
      funext lane
      fin_cases lane <;> with_unfolding_all rfl
    exact congrFun (he.trans ht.symm)
#print axioms empty
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4820.withdrawal.c.states 11)) (appSibR (wordPublic withdrawalPublic) 15) (appBitR (wordPublic withdrawalPublic) 15) = (left,right) := by
  change (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode4820.withdrawal.c.states 11),PV_Src_CanonicalRoots.table.val[15]!) = _
  rw [empty]
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 49 = (left,right) := by
  change orderedR (okOr (appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15) zero8) (appSibR (wordPublic withdrawalPublic) 15) (appBitR (wordPublic withdrawalPublic) 15) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← appCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15
    let o := orderedR cur (appSibR (wordPublic withdrawalPublic) 15) (appBitR (wordPublic withdrawalPublic) 15)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 49 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 49 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 49).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 49).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell7620.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[49]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 49 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode4920.withdrawal
