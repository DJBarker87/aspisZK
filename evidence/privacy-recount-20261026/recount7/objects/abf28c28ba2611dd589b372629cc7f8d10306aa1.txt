import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes0920
import R1Z.PV_RunJoin_CopyGroup0920
import R1Z.PV_RunJoin_CopyGroup1820
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1320.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1519.certificate
def left : Array U32 8#usize := Array.make 8#usize [2161#u32,2178#u32,2195#u32,2212#u32,2229#u32,2246#u32,2263#u32,2280#u32]
def right : Array U32 8#usize := Array.make 8#usize [785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,617980080#u32]

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
        change ¬ 2147483647 ≤ 617980080 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1520.canon PV_RunJoin_CopyCell1520.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 9 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1220.transfer.c.states 11)) := PV_RunJoin_SourceNode1220.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1220.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[9]!) (bitB (wordWitness transferWitness) 9) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 13 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 9) zero8) ((wordWitness transferWitness).sibs.val[9]!) (bitB (wordWitness transferWitness) 9) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 10 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 9
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[9]!) (bitB (wordWitness transferWitness) 9)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 13 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 13 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 13).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 13).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1520.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[13]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 13 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1320.transfer
namespace R1Z.PV_RunJoin_SourceNode1320.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1519.certificate
def left : Array U32 8#usize := Array.make 8#usize [2161#u32,2178#u32,2195#u32,2212#u32,2229#u32,2246#u32,2263#u32,2280#u32]
def right : Array U32 8#usize := Array.make 8#usize [785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,617980080#u32]

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
        change ¬ 2147483647 ≤ 617980080 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1520.canon PV_RunJoin_CopyCell1520.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1220.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1220.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1220.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[9]!) (bitB (wordWitness withdrawalWitness) 9) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9) zero8) ((wordWitness withdrawalWitness).sibs.val[9]!) (bitB (wordWitness withdrawalWitness) 9) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[9]!) (bitB (wordWitness withdrawalWitness) 9)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 13 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 13 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1520.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[13]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 13 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1320.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1420.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1619.certificate
def left : Array U32 8#usize := Array.make 8#usize [2181#u32,2198#u32,2215#u32,2232#u32,2249#u32,2266#u32,2283#u32,2300#u32]
def right : Array U32 8#usize := Array.make 8#usize [1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,1614233662#u32]

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
        change 2147483647 ≤ 1614233662 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1620.canon PV_RunJoin_CopyCell1620.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 10 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1320.transfer.c.states 11)) := PV_RunJoin_SourceNode1320.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1320.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[10]!) (bitB (wordWitness transferWitness) 10) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 14 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 10) zero8) ((wordWitness transferWitness).sibs.val[10]!) (bitB (wordWitness transferWitness) 10) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 11 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 10
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[10]!) (bitB (wordWitness transferWitness) 10)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 14 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 14 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 14).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 14).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1620.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[14]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 14 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1420.transfer
namespace R1Z.PV_RunJoin_SourceNode1420.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1619.certificate
def left : Array U32 8#usize := Array.make 8#usize [2181#u32,2198#u32,2215#u32,2232#u32,2249#u32,2266#u32,2283#u32,2300#u32]
def right : Array U32 8#usize := Array.make 8#usize [1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,1614233662#u32]

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
        change 2147483647 ≤ 1614233662 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1620.canon PV_RunJoin_CopyCell1620.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1320.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1320.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1320.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[10]!) (bitB (wordWitness withdrawalWitness) 10) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10) zero8) ((wordWitness withdrawalWitness).sibs.val[10]!) (bitB (wordWitness withdrawalWitness) 10) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[10]!) (bitB (wordWitness withdrawalWitness) 10)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 14 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 14 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1620.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[14]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 14 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1420.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1520.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1719.certificate
def left : Array U32 8#usize := Array.make 8#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,1359169338#u32,1742041081#u32,1575185854#u32,1782871725#u32]
def right : Array U32 8#usize := Array.make 8#usize [2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,2320#u32]

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
        change ¬ 2147483647 ≤ 2320 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1720.canon PV_RunJoin_CopyCell1720.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 11 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1420.transfer.c.states 11)) := PV_RunJoin_SourceNode1420.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1420.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[11]!) (bitB (wordWitness transferWitness) 11) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 15 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 11) zero8) ((wordWitness transferWitness).sibs.val[11]!) (bitB (wordWitness transferWitness) 11) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 12 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 11
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[11]!) (bitB (wordWitness transferWitness) 11)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 15 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 15 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 15).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 15).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1720.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[15]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 15 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1520.transfer
namespace R1Z.PV_RunJoin_SourceNode1520.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1719.certificate
def left : Array U32 8#usize := Array.make 8#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,1359169338#u32,1742041081#u32,1575185854#u32,1782871725#u32]
def right : Array U32 8#usize := Array.make 8#usize [2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,2320#u32]

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
        change ¬ 2147483647 ≤ 2320 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1720.canon PV_RunJoin_CopyCell1720.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1420.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1420.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1420.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[11]!) (bitB (wordWitness withdrawalWitness) 11) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11) zero8) ((wordWitness withdrawalWitness).sibs.val[11]!) (bitB (wordWitness withdrawalWitness) 11) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[11]!) (bitB (wordWitness withdrawalWitness) 11)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 15 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 15 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1720.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[15]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 15 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1520.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1620.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1819.certificate
def left : Array U32 8#usize := Array.make 8#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,1994057985#u32,1261374148#u32,1230772006#u32,1621463387#u32]
def right : Array U32 8#usize := Array.make 8#usize [2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,2340#u32]

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
        change ¬ 2147483647 ≤ 2340 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1820.canon PV_RunJoin_CopyCell1820.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 12 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1520.transfer.c.states 11)) := PV_RunJoin_SourceNode1520.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1520.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[12]!) (bitB (wordWitness transferWitness) 12) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 16 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 12) zero8) ((wordWitness transferWitness).sibs.val[12]!) (bitB (wordWitness transferWitness) 12) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 13 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 12
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[12]!) (bitB (wordWitness transferWitness) 12)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 16 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 16 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 16).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 16).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1820.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[16]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 16 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1620.transfer
namespace R1Z.PV_RunJoin_SourceNode1620.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1819.certificate
def left : Array U32 8#usize := Array.make 8#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,1994057985#u32,1261374148#u32,1230772006#u32,1621463387#u32]
def right : Array U32 8#usize := Array.make 8#usize [2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,2340#u32]

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
        change ¬ 2147483647 ≤ 2340 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1820.canon PV_RunJoin_CopyCell1820.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1520.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1520.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1520.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[12]!) (bitB (wordWitness withdrawalWitness) 12) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12) zero8) ((wordWitness withdrawalWitness).sibs.val[12]!) (bitB (wordWitness withdrawalWitness) 12) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[12]!) (bitB (wordWitness withdrawalWitness) 12)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 16 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 16 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1820.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[16]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 16 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1620.withdrawal
