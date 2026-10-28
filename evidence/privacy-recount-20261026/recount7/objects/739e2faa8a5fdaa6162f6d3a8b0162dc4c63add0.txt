import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes2120
import R1Z.PV_RunJoin_CopyGroup2720
import R1Z.PV_RunJoin_CopyGroup3620
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode5420.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2719.certificate
def left : Array U32 8#usize := Array.make 8#usize [3001#u32,3018#u32,3035#u32,3052#u32,3069#u32,3086#u32,3103#u32,3120#u32]
def right : Array U32 8#usize := Array.make 8#usize [9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,1485431753#u32]

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
        change 2147483647 ≤ 1485431753 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2720.canon PV_RunJoin_CopyCell2720.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 21 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2420.transfer.c.states 11)) := PV_RunJoin_SourceNode2420.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2420.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[21]!) (bitB (wordWitness transferWitness) 21) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 54 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 21) zero8) ((wordWitness transferWitness).sibs.val[21]!) (bitB (wordWitness transferWitness) 21) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 22 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 21
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[21]!) (bitB (wordWitness transferWitness) 21)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 54 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 54 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 54).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 54).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2720.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[54]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 54 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5420.transfer
namespace R1Z.PV_RunJoin_SourceNode5420.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2719.certificate
def left : Array U32 8#usize := Array.make 8#usize [3001#u32,3018#u32,3035#u32,3052#u32,3069#u32,3086#u32,3103#u32,3120#u32]
def right : Array U32 8#usize := Array.make 8#usize [9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,1485431753#u32]

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
        change 2147483647 ≤ 1485431753 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2720.canon PV_RunJoin_CopyCell2720.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 21 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2420.withdrawal.c.states 11)) := PV_RunJoin_SourceNode2420.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2420.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[21]!) (bitB (wordWitness withdrawalWitness) 21) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 54 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 21) zero8) ((wordWitness withdrawalWitness).sibs.val[21]!) (bitB (wordWitness withdrawalWitness) 21) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 22 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 21
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[21]!) (bitB (wordWitness withdrawalWitness) 21)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 54 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 54 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 54).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 54).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2720.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[54]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 54 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5420.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode5520.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2819.certificate
def left : Array U32 8#usize := Array.make 8#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,159927545#u32,2111428769#u32,132405182#u32]
def right : Array U32 8#usize := Array.make 8#usize [3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,3220#u32]

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
        change ¬ 2147483647 ≤ 3220 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2820.canon PV_RunJoin_CopyCell2820.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 22 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5420.transfer.c.states 11)) := PV_RunJoin_SourceNode5420.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5420.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[22]!) (bitB (wordWitness transferWitness) 22) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 55 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 22) zero8) ((wordWitness transferWitness).sibs.val[22]!) (bitB (wordWitness transferWitness) 22) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 23 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 22
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[22]!) (bitB (wordWitness transferWitness) 22)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 55 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 55 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 55).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 55).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2820.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[55]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 55 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5520.transfer
namespace R1Z.PV_RunJoin_SourceNode5520.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2819.certificate
def left : Array U32 8#usize := Array.make 8#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,159927545#u32,2111428769#u32,132405182#u32]
def right : Array U32 8#usize := Array.make 8#usize [3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,3220#u32]

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
        change ¬ 2147483647 ≤ 3220 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2820.canon PV_RunJoin_CopyCell2820.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 22 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5420.withdrawal.c.states 11)) := PV_RunJoin_SourceNode5420.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5420.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[22]!) (bitB (wordWitness withdrawalWitness) 22) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 55 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 22) zero8) ((wordWitness withdrawalWitness).sibs.val[22]!) (bitB (wordWitness withdrawalWitness) 22) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 23 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 22
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[22]!) (bitB (wordWitness withdrawalWitness) 22)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 55 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 55 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 55).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 55).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2820.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[55]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 55 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5520.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode5620.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2919.certificate
def left : Array U32 8#usize := Array.make 8#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,3286#u32,3303#u32,3320#u32]
def right : Array U32 8#usize := Array.make 8#usize [407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,1368876468#u32]

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
        change 2147483647 ≤ 1368876468 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2920.canon PV_RunJoin_CopyCell2920.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 23 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5520.transfer.c.states 11)) := PV_RunJoin_SourceNode5520.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5520.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[23]!) (bitB (wordWitness transferWitness) 23) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 56 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 23) zero8) ((wordWitness transferWitness).sibs.val[23]!) (bitB (wordWitness transferWitness) 23) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 24 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 23
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[23]!) (bitB (wordWitness transferWitness) 23)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 56 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 56 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 56).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 56).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[56]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 56 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5620.transfer
namespace R1Z.PV_RunJoin_SourceNode5620.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2919.certificate
def left : Array U32 8#usize := Array.make 8#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,3286#u32,3303#u32,3320#u32]
def right : Array U32 8#usize := Array.make 8#usize [407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,1368876468#u32]

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
        change 2147483647 ≤ 1368876468 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2920.canon PV_RunJoin_CopyCell2920.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 23 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5520.withdrawal.c.states 11)) := PV_RunJoin_SourceNode5520.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode5520.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[23]!) (bitB (wordWitness withdrawalWitness) 23) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 56 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 23) zero8) ((wordWitness withdrawalWitness).sibs.val[23]!) (bitB (wordWitness withdrawalWitness) 23) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 24 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 23
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[23]!) (bitB (wordWitness withdrawalWitness) 23)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 56 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 56 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 56).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 56).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[56]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 56 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode5620.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode3320.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell3919.certificate
def left : Array U32 8#usize := Array.make 8#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,420127778#u32,800761649#u32,949547039#u32,74873928#u32]
def right : Array U32 8#usize := Array.make 8#usize [109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,351017421#u32]

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
        change ¬ 2147483647 ≤ 351017421 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell3920.canon PV_RunJoin_CopyCell3920.models
#print axioms node
theorem recipient : recipDR (wordWitness transferWitness) (wordPublic transferPublic) = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceSponge2920.transfer.c.states 11)) := by
  rw [recipDR,noteDigestR]
  change (do
    let p ← spongePre (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 29
    spongeDigestR p ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).schunk 29) ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).sclen 29)) = _
  rw [PV_RunJoin_SourceSponge2920.transfer.pre]
  simp only [bind_tc_ok]
  exact PV_RunJoin_SourceSponge2920.transfer.digest
#print axioms recipient
theorem change : changeDR (wordWitness transferWitness) (wordPublic transferPublic) = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceSponge3220.transfer.c.states 11)) := by
  rw [changeDR,noteDigestR]
  change (do
    let p ← spongePre (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 32
    spongeDigestR p ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).schunk 32) ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).sclen 32)) = _
  rw [PV_RunJoin_SourceSponge3220.transfer.pre]
  simp only [bind_tc_ok]
  exact PV_RunJoin_SourceSponge3220.transfer.digest
#print axioms change
theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 33 = (left,right) := by
  change (okOr (recipDR (wordWitness transferWitness) (wordPublic transferPublic)) zero8,okOr (changeDR (wordWitness transferWitness) (wordPublic transferPublic)) zero8) = _
  rw [recipient,change,okOr_ok,okOr_ok]
  with_unfolding_all rfl
#print axioms children

theorem next : outPairR (wordWitness transferWitness) (wordPublic transferPublic) = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let r ← recipDR (wordWitness transferWitness) (wordPublic transferPublic)
    let c ← changeDR (wordWitness transferWitness) (wordPublic transferPublic)
    nodeDigestR r c) = _
  rw [recipient]
  simp only [bind_tc_ok]
  rw [change]
  simp only [bind_tc_ok]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 33 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 33 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 33).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 33).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell3920.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[33]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 33 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3320.transfer
namespace R1Z.PV_RunJoin_SourceNode3320.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell4019.certificate
def left : Array U32 8#usize := Array.make 8#usize [263935107#u32,2015801952#u32,2126421827#u32,1338328324#u32,66681051#u32,462846977#u32,1805190326#u32,1770497381#u32]
def right : Array U32 8#usize := Array.make 8#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]

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
        change ¬ 2147483647 ≤ 0 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell4020.canon PV_RunJoin_CopyCell4020.models
#print axioms node
theorem change : changeDR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceSponge3220.withdrawal.c.states 11)) := by
  rw [changeDR,noteDigestR]
  change (do
    let p ← spongePre (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 32
    spongeDigestR p ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).schunk 32) ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).sclen 32)) = _
  rw [PV_RunJoin_SourceSponge3220.withdrawal.pre]
  simp only [bind_tc_ok]
  exact PV_RunJoin_SourceSponge3220.withdrawal.digest
#print axioms change
theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 33 = (left,right) := by
  change (okOr (changeDR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) zero8,zero8) = _
  rw [change,okOr_ok]
  with_unfolding_all rfl
#print axioms children

theorem next : outPairR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let c ← changeDR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)
    nodeDigestR c zero8) = _
  rw [change]
  simp only [bind_tc_ok]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 33 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 33 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 33).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 33).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell4020.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[33]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 33 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode3320.withdrawal
