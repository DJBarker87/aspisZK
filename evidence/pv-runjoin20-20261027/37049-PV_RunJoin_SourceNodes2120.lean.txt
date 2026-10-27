import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes1720
import R1Z.PV_RunJoin_CopyGroup1820
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode2120.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2319.certificate
def left : Array U32 8#usize := Array.make 8#usize [2321#u32,2338#u32,2355#u32,2372#u32,2389#u32,2406#u32,2423#u32,2440#u32]
def right : Array U32 8#usize := Array.make 8#usize [1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,1092402184#u32]

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
        change 2147483647 ≤ 1092402184 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2320.canon PV_RunJoin_CopyCell2320.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 17 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2020.transfer.c.states 11)) := PV_RunJoin_SourceNode2020.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2020.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[17]!) (bitB (wordWitness transferWitness) 17) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 21 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 17) zero8) ((wordWitness transferWitness).sibs.val[17]!) (bitB (wordWitness transferWitness) 17) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 18 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 17
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[17]!) (bitB (wordWitness transferWitness) 17)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 21 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 21 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 21).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 21).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[21]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 21 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2120.transfer
namespace R1Z.PV_RunJoin_SourceNode2120.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2319.certificate
def left : Array U32 8#usize := Array.make 8#usize [2321#u32,2338#u32,2355#u32,2372#u32,2389#u32,2406#u32,2423#u32,2440#u32]
def right : Array U32 8#usize := Array.make 8#usize [1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,1092402184#u32]

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
        change 2147483647 ≤ 1092402184 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2320.canon PV_RunJoin_CopyCell2320.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2020.withdrawal.c.states 11)) := PV_RunJoin_SourceNode2020.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2020.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[17]!) (bitB (wordWitness withdrawalWitness) 17) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 21 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17) zero8) ((wordWitness withdrawalWitness).sibs.val[17]!) (bitB (wordWitness withdrawalWitness) 17) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 17
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[17]!) (bitB (wordWitness withdrawalWitness) 17)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 21 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 21 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 21).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 21).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[21]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 21 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2120.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode2220.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2419.certificate
def left : Array U32 8#usize := Array.make 8#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,2134488188#u32,1020968422#u32,1342497638#u32,1907691591#u32]
def right : Array U32 8#usize := Array.make 8#usize [2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,2460#u32]

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
        change ¬ 2147483647 ≤ 2460 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2420.canon PV_RunJoin_CopyCell2420.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 18 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2120.transfer.c.states 11)) := PV_RunJoin_SourceNode2120.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2120.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[18]!) (bitB (wordWitness transferWitness) 18) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 22 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 18) zero8) ((wordWitness transferWitness).sibs.val[18]!) (bitB (wordWitness transferWitness) 18) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 19 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 18
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[18]!) (bitB (wordWitness transferWitness) 18)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 22 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 22 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 22).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 22).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[22]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 22 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2220.transfer
namespace R1Z.PV_RunJoin_SourceNode2220.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2419.certificate
def left : Array U32 8#usize := Array.make 8#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,2134488188#u32,1020968422#u32,1342497638#u32,1907691591#u32]
def right : Array U32 8#usize := Array.make 8#usize [2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,2460#u32]

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
        change ¬ 2147483647 ≤ 2460 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2420.canon PV_RunJoin_CopyCell2420.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2120.withdrawal.c.states 11)) := PV_RunJoin_SourceNode2120.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2120.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[18]!) (bitB (wordWitness withdrawalWitness) 18) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 22 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18) zero8) ((wordWitness withdrawalWitness).sibs.val[18]!) (bitB (wordWitness withdrawalWitness) 18) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 18
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[18]!) (bitB (wordWitness withdrawalWitness) 18)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 22 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 22 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 22).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 22).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[22]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 22 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2220.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode2320.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2519.certificate
def left : Array U32 8#usize := Array.make 8#usize [2361#u32,2378#u32,2395#u32,2412#u32,2429#u32,2446#u32,2463#u32,2480#u32]
def right : Array U32 8#usize := Array.make 8#usize [2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,132339882#u32]

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
        change ¬ 2147483647 ≤ 132339882 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2520.canon PV_RunJoin_CopyCell2520.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 19 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2220.transfer.c.states 11)) := PV_RunJoin_SourceNode2220.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2220.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[19]!) (bitB (wordWitness transferWitness) 19) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 23 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 19) zero8) ((wordWitness transferWitness).sibs.val[19]!) (bitB (wordWitness transferWitness) 19) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 20 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 19
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[19]!) (bitB (wordWitness transferWitness) 19)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 23 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 23 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 23).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 23).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2520.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[23]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 23 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2320.transfer
namespace R1Z.PV_RunJoin_SourceNode2320.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2519.certificate
def left : Array U32 8#usize := Array.make 8#usize [2361#u32,2378#u32,2395#u32,2412#u32,2429#u32,2446#u32,2463#u32,2480#u32]
def right : Array U32 8#usize := Array.make 8#usize [2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,132339882#u32]

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
        change ¬ 2147483647 ≤ 132339882 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2520.canon PV_RunJoin_CopyCell2520.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2220.withdrawal.c.states 11)) := PV_RunJoin_SourceNode2220.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2220.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[19]!) (bitB (wordWitness withdrawalWitness) 19) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 23 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19) zero8) ((wordWitness withdrawalWitness).sibs.val[19]!) (bitB (wordWitness withdrawalWitness) 19) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 19
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[19]!) (bitB (wordWitness withdrawalWitness) 19)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 23 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 23 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 23).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 23).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2520.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[23]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 23 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2320.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode2420.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2619.certificate
def left : Array U32 8#usize := Array.make 8#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,1217412274#u32,1723220283#u32,85709078#u32,537745032#u32]
def right : Array U32 8#usize := Array.make 8#usize [2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,2500#u32]

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
        change ¬ 2147483647 ≤ 2500 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2620.canon PV_RunJoin_CopyCell2620.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 20 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2320.transfer.c.states 11)) := PV_RunJoin_SourceNode2320.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2320.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[20]!) (bitB (wordWitness transferWitness) 20) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 24 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 20) zero8) ((wordWitness transferWitness).sibs.val[20]!) (bitB (wordWitness transferWitness) 20) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 21 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 20
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[20]!) (bitB (wordWitness transferWitness) 20)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 24 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 24 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 24).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 24).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2620.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[24]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 24 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2420.transfer
namespace R1Z.PV_RunJoin_SourceNode2420.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell2619.certificate
def left : Array U32 8#usize := Array.make 8#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,1217412274#u32,1723220283#u32,85709078#u32,537745032#u32]
def right : Array U32 8#usize := Array.make 8#usize [2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,2500#u32]

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
        change ¬ 2147483647 ≤ 2500 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell2620.canon PV_RunJoin_CopyCell2620.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2320.withdrawal.c.states 11)) := PV_RunJoin_SourceNode2320.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode2320.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[20]!) (bitB (wordWitness withdrawalWitness) 20) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 24 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20) zero8) ((wordWitness withdrawalWitness).sibs.val[20]!) (bitB (wordWitness withdrawalWitness) 20) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 21 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 20
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[20]!) (bitB (wordWitness withdrawalWitness) 20)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 24 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 24 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 24).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 24).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell2620.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[24]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 24 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode2420.withdrawal
