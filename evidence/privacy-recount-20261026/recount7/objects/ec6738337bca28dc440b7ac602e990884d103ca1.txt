import R1Z.PV_RunJoin_NodeExecution20
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3220
import R1Z.PV_RunJoin_ZeroConstructor18
import R1Z.PV_RunJoin_SourceNodes0520
import R1Z.PV_RunJoin_CopyGroup0920
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode0920.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1119.certificate
def left : Array U32 8#usize := Array.make 8#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,389529953#u32,896398700#u32]
def right : Array U32 8#usize := Array.make 8#usize [2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,2200#u32]

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
        change ¬ 2147483647 ≤ 2200 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1120.canon PV_RunJoin_CopyCell1120.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 5 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0820.transfer.c.states 11)) := PV_RunJoin_SourceNode0820.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0820.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[5]!) (bitB (wordWitness transferWitness) 5) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 9 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 5) zero8) ((wordWitness transferWitness).sibs.val[5]!) (bitB (wordWitness transferWitness) 5) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 6 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 5
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[5]!) (bitB (wordWitness transferWitness) 5)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 9 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 9 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 9).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 9).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[9]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 9 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode0920.transfer
namespace R1Z.PV_RunJoin_SourceNode0920.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1119.certificate
def left : Array U32 8#usize := Array.make 8#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,389529953#u32,896398700#u32]
def right : Array U32 8#usize := Array.make 8#usize [2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,2200#u32]

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
        change ¬ 2147483647 ≤ 2200 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1120.canon PV_RunJoin_CopyCell1120.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 5 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0820.withdrawal.c.states 11)) := PV_RunJoin_SourceNode0820.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0820.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[5]!) (bitB (wordWitness withdrawalWitness) 5) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 5) zero8) ((wordWitness withdrawalWitness).sibs.val[5]!) (bitB (wordWitness withdrawalWitness) 5) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 6 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 5
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[5]!) (bitB (wordWitness withdrawalWitness) 5)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 9 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 9 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1120.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[9]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 9 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode0920.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1020.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1219.certificate
def left : Array U32 8#usize := Array.make 8#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,2186#u32,2203#u32,2220#u32]
def right : Array U32 8#usize := Array.make 8#usize [439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,1763090787#u32]

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
        change 2147483647 ≤ 1763090787 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1220.canon PV_RunJoin_CopyCell1220.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 6 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0920.transfer.c.states 11)) := PV_RunJoin_SourceNode0920.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0920.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[6]!) (bitB (wordWitness transferWitness) 6) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 10 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 6) zero8) ((wordWitness transferWitness).sibs.val[6]!) (bitB (wordWitness transferWitness) 6) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 7 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 6
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[6]!) (bitB (wordWitness transferWitness) 6)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 10 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 10 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 10).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 10).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[10]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 10 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1020.transfer
namespace R1Z.PV_RunJoin_SourceNode1020.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1219.certificate
def left : Array U32 8#usize := Array.make 8#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,2186#u32,2203#u32,2220#u32]
def right : Array U32 8#usize := Array.make 8#usize [439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,1763090787#u32]

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
        change 2147483647 ≤ 1763090787 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1220.canon PV_RunJoin_CopyCell1220.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 6 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0920.withdrawal.c.states 11)) := PV_RunJoin_SourceNode0920.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode0920.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[6]!) (bitB (wordWitness withdrawalWitness) 6) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 6) zero8) ((wordWitness withdrawalWitness).sibs.val[6]!) (bitB (wordWitness withdrawalWitness) 6) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 7 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 6
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[6]!) (bitB (wordWitness withdrawalWitness) 6)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 10 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 10 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 10).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1220.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[10]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 10 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1020.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1120.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1319.certificate
def left : Array U32 8#usize := Array.make 8#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,1175699129#u32,1224545956#u32,757035799#u32]
def right : Array U32 8#usize := Array.make 8#usize [2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,2240#u32]

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
        change ¬ 2147483647 ≤ 2240 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1320.canon PV_RunJoin_CopyCell1320.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 7 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1020.transfer.c.states 11)) := PV_RunJoin_SourceNode1020.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1020.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[7]!) (bitB (wordWitness transferWitness) 7) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 11 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 7) zero8) ((wordWitness transferWitness).sibs.val[7]!) (bitB (wordWitness transferWitness) 7) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 8 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 7
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[7]!) (bitB (wordWitness transferWitness) 7)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 11 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 11 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 11).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 11).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[11]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 11 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1120.transfer
namespace R1Z.PV_RunJoin_SourceNode1120.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1319.certificate
def left : Array U32 8#usize := Array.make 8#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,1175699129#u32,1224545956#u32,757035799#u32]
def right : Array U32 8#usize := Array.make 8#usize [2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,2240#u32]

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
        change ¬ 2147483647 ≤ 2240 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1320.canon PV_RunJoin_CopyCell1320.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 7 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1020.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1020.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1020.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[7]!) (bitB (wordWitness withdrawalWitness) 7) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 7) zero8) ((wordWitness withdrawalWitness).sibs.val[7]!) (bitB (wordWitness withdrawalWitness) 7) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 8 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 7
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[7]!) (bitB (wordWitness withdrawalWitness) 7)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 11 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 11 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 11).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[11]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 11 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1120.withdrawal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceNode1220.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1419.certificate
def left : Array U32 8#usize := Array.make 8#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,896074385#u32,533821444#u32,2118230281#u32,1863638021#u32]
def right : Array U32 8#usize := Array.make 8#usize [2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,2260#u32]

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
        change ¬ 2147483647 ≤ 2260 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1420.canon PV_RunJoin_CopyCell1420.models
#print axioms node
theorem cursor : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 8 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1120.transfer.c.states 11)) := PV_RunJoin_SourceNode1120.transfer.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1120.transfer.c.states 11)) ((wordWitness transferWitness).sibs.val[8]!) (bitB (wordWitness transferWitness) 8) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 12 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 8) zero8) ((wordWitness transferWitness).sibs.val[8]!) (bitB (wordWitness transferWitness) 8) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 9 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness transferWitness) (wordPublic transferPublic) 8
    let o := orderedR cur ((wordWitness transferWitness).sibs.val[8]!) (bitB (wordWitness transferWitness) 8)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 12 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain transferWitness transferPublic 12 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 12).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness transferWitness) (wordPublic transferPublic) 12).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[12]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 12 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1220.transfer
namespace R1Z.PV_RunJoin_SourceNode1220.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell1419.certificate
def left : Array U32 8#usize := Array.make 8#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,896074385#u32,533821444#u32,2118230281#u32,1863638021#u32]
def right : Array U32 8#usize := Array.make 8#usize [2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,2260#u32]

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
        change ¬ 2147483647 ≤ 2260 + 1095962629
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
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell1420.canon PV_RunJoin_CopyCell1420.models
#print axioms node
theorem cursor : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 8 = ok (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1120.withdrawal.c.states 11)) := PV_RunJoin_SourceNode1120.withdrawal.next
#print axioms cursor
theorem ordered : orderedR (R0Z.WriterRefine.digest8 (PV_RunJoin_SourceNode1120.withdrawal.c.states 11)) ((wordWitness withdrawalWitness).sibs.val[8]!) (bitB (wordWitness withdrawalWitness) 8) = (left,right) := by
  with_unfolding_all rfl
#print axioms ordered

theorem children : childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12 = (left,right) := by
  change orderedR (okOr (treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 8) zero8) ((wordWitness withdrawalWitness).sibs.val[8]!) (bitB (wordWitness withdrawalWitness) 8) = _
  rw [cursor,okOr_ok]
  exact ordered
#print axioms children

theorem next : treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 9 = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  change (do
    let cur ← treeCurR (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 8
    let o := orderedR cur ((wordWitness withdrawalWitness).sibs.val[8]!) (bitB (wordWitness withdrawalWitness) 8)
    nodeDigestR o.1 o.2) = _
  rw [cursor]
  simp only [bind_tc_ok]
  rw [ordered]
  exact node
#print axioms next
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 12 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  apply PV_RunJoin_NodeExecution20.chain withdrawalWitness withdrawalPublic 12 c (by decide)
  · change R0BlockCopies.node_pre (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12).2 = _
    rw [children]
    exact pre
  · change R0BlockCopies.node_absorb (childrenOf (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) 12).1 = _
    rw [children]
    exact absorb
  · exact PV_RunJoin_CopyCell1420.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[12]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 12 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceNode1220.withdrawal
