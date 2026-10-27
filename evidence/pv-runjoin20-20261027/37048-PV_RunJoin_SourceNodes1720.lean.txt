import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes1320
import R1Z.PV_RunJoin_CopyGroup1820
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1720.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1919.certificate
def left : Array U32 8#usize := Array.make 8#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,70404971#u32,1215624494#u32,880337038#u32,1016952666#u32]
def right : Array U32 8#usize := Array.make 8#usize [2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,2360#u32]

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
        change ¬ 2147483647 ≤ 2360 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1920.canon PV_RunJoin_CopyCell1920.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 13 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1620.transfer.c.states 11)) := PV_RunJoin_SourceNode1620.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1620.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[13]!) (bitB (wordWitness transferWitness) 13) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 17 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 13) zero8) ((wordWitness transferWitness).sibs.val[13]!) (bitB (wordWitness transferWitness) 13) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 14 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 13
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[13]!) (bitB (wordWitness transferWitness) 13)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 17 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 17 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 17).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 17).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[17]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 17 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1720.transfer
namespace R1Z.PV_RunJoin_SourceNode1720.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1919.certificate
def left : Array U32 8#usize := Array.make 8#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,70404971#u32,1215624494#u32,880337038#u32,1016952666#u32]
def right : Array U32 8#usize := Array.make 8#usize [2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,2360#u32]

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
        change ¬ 2147483647 ≤ 2360 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1920.canon PV_RunJoin_CopyCell1920.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1620.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1620.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1620.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[13]!) (bitB (wordWitness withdrawalWitness) 13) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13) zero8) ((wordWitness withdrawalWitness).sibs.val[13]!) (bitB (wordWitness withdrawalWitness) 13) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 13
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[13]!) (bitB (wordWitness withdrawalWitness) 13)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 17 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 17 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[17]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 17 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1720.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1820.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2019.certificate
def left : Array U32 8#usize := Array.make 8#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,1601727123#u32,1630516452#u32,660958964#u32,1526316434#u32]
def right : Array U32 8#usize := Array.make 8#usize [2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,2380#u32]

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
        change ¬ 2147483647 ≤ 2380 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2020.canon PV_RunJoin_CopyCell2020.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 14 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1720.transfer.c.states 11)) := PV_RunJoin_SourceNode1720.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1720.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[14]!) (bitB (wordWitness transferWitness) 14) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 18 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 14) zero8) ((wordWitness transferWitness).sibs.val[14]!) (bitB (wordWitness transferWitness) 14) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 15 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 14
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[14]!) (bitB (wordWitness transferWitness) 14)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 18 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 18 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 18).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 18).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2020.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[18]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 18 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1820.transfer
namespace R1Z.PV_RunJoin_SourceNode1820.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2019.certificate
def left : Array U32 8#usize := Array.make 8#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,1601727123#u32,1630516452#u32,660958964#u32,1526316434#u32]
def right : Array U32 8#usize := Array.make 8#usize [2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,2380#u32]

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
        change ¬ 2147483647 ≤ 2380 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2020.canon PV_RunJoin_CopyCell2020.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1720.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1720.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1720.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[14]!) (bitB (wordWitness withdrawalWitness) 14) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14) zero8) ((wordWitness withdrawalWitness).sibs.val[14]!) (bitB (wordWitness withdrawalWitness) 14) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 14
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[14]!) (bitB (wordWitness withdrawalWitness) 14)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 18 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 18 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2020.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[18]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 18 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1820.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1920.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2119.certificate
def left : Array U32 8#usize := Array.make 8#usize [2281#u32,2298#u32,2315#u32,2332#u32,2349#u32,2366#u32,2383#u32,2400#u32]
def right : Array U32 8#usize := Array.make 8#usize [493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,346637554#u32]

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
        change ¬ 2147483647 ≤ 346637554 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2120.canon PV_RunJoin_CopyCell2120.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 15 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1820.transfer.c.states 11)) := PV_RunJoin_SourceNode1820.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1820.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[15]!) (bitB (wordWitness transferWitness) 15) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 19 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 15) zero8) ((wordWitness transferWitness).sibs.val[15]!) (bitB (wordWitness transferWitness) 15) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 16 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 15
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[15]!) (bitB (wordWitness transferWitness) 15)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 19 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 19 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 19).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 19).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[19]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 19 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1920.transfer
namespace R1Z.PV_RunJoin_SourceNode1920.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2119.certificate
def left : Array U32 8#usize := Array.make 8#usize [2281#u32,2298#u32,2315#u32,2332#u32,2349#u32,2366#u32,2383#u32,2400#u32]
def right : Array U32 8#usize := Array.make 8#usize [493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,346637554#u32]

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
        change ¬ 2147483647 ≤ 346637554 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2120.canon PV_RunJoin_CopyCell2120.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1820.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1820.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1820.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[15]!) (bitB (wordWitness withdrawalWitness) 15) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15) zero8) ((wordWitness withdrawalWitness).sibs.val[15]!) (bitB (wordWitness withdrawalWitness) 15) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 15
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[15]!) (bitB (wordWitness withdrawalWitness) 15)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 19 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 19 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[19]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 19 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1920.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode2020.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2219.certificate
def left : Array U32 8#usize := Array.make 8#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,1017414220#u32,839141147#u32,732445005#u32,1267400728#u32]
def right : Array U32 8#usize := Array.make 8#usize [2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,2420#u32]

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
        change ¬ 2147483647 ≤ 2420 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2220.canon PV_RunJoin_CopyCell2220.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 16 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1920.transfer.c.states 11)) := PV_RunJoin_SourceNode1920.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1920.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[16]!) (bitB (wordWitness transferWitness) 16) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 20 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 16) zero8) ((wordWitness transferWitness).sibs.val[16]!) (bitB (wordWitness transferWitness) 16) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 17 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 16
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[16]!) (bitB (wordWitness transferWitness) 16)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 20 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 20 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 20).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 20).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[20]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 20 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2020.transfer
namespace R1Z.PV_RunJoin_SourceNode2020.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2219.certificate
def left : Array U32 8#usize := Array.make 8#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,1017414220#u32,839141147#u32,732445005#u32,1267400728#u32]
def right : Array U32 8#usize := Array.make 8#usize [2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,2420#u32]

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
        change ¬ 2147483647 ≤ 2420 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2220.canon PV_RunJoin_CopyCell2220.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1920.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1920.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1920.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[16]!) (bitB (wordWitness withdrawalWitness) 16) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16) zero8) ((wordWitness withdrawalWitness).sibs.val[16]!) (bitB (wordWitness withdrawalWitness) 16) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 16
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[16]!) (bitB (wordWitness withdrawalWitness) 16)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 20 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 20 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[20]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 20 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2020.withdrawal
