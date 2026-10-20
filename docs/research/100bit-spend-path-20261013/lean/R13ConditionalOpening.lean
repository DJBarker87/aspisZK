import R13LeafSlices
import R13PaddedLeafPrograms
import R13SourceTerminal

/-! Conditional consumer joining the source leaf fact and Bin multiproof.
The explicit `modelAccept` hypothesis is the unproved array-loop simulation
output. This theorem is not accepted-source-run implies model acceptance. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.R13ConditionalOpening
open AspisR1Stage2 AspisR1Stage2.WireTx2
open BinMerkle32Path BinMultiproof R13WireToBin R13LeafSlices
open AspisV8R19.MemoizedProgramLaw

theorem opening_program (ops : LeafOps) (saltLaw : SaltLaw ops)
    (leafLaw : LeafDigestLaw ops)
    (c1 : ops.c1Tag = ok 113#u8) (c2 : ops.c2Tag = ok 241#u8)
    {T : Type} (D : aspis_core.digest.Digest32 T) (hash : T)
    (H : List BinMerkle32Path.Byte → Digest) (law : DigestLaw D hash H)
    (tree : Usize) (q : Slice U8) (out : Bytes32)
    (sourceLeaf : verifier.candidate.batch_leafWithWireOps ops D hash tree q = ok out)
    {root : Digest} {depth : Nat} {active : Active} {v : BinMultiproof.Values}
    {count capacity index : Nat} {stored : List Digest} {trace : List (List BinMerkle32Path.Byte)}
    {batch canonical : List BinBatchDedup.Entry}
    (dedupRun : BinBatchDedup.run batch = some canonical)
    (represented : Dedup canonical active v)
    (member : (index, digest out) ∈ batch)
    (modelAccept : PaddedAccept H root depth active v count capacity stored trace) :
    count = nodeCount depth active ∧ ∃ path : Path (slots depth index),
      (eval H (BinMerkleProgram.leafProgram path (leafFor tree q))).2 = root ∧
      inputTrace H path (H (leafFor tree q)) ⊆ trace := by
  have leafEq := source_leaf_exact ops saltLaw leafLaw c1 c2 D hash H law tree q out sourceLeaf
  obtain ⟨path, hp, ht⟩ := BinBatchDedup.accepted_original_queries dedupRun represented
    modelAccept.2.2.2 _ member
  rw [leafEq] at hp ht
  exact ⟨padded_exact_count modelAccept, path,
    (BinMerkleProgram.leafProgram_accepts_iff H path (leafFor tree q) root).mpr hp, ht⟩

#print axioms opening_program
end AspisR1.R13ConditionalOpening
