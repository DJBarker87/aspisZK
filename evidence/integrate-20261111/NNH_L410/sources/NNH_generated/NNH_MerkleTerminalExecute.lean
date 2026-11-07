import NNH_MerkleLevelsExecute
import NLL_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleTerminalExecute
open Aeneas Aeneas.Std NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

def count (s : MultiproofConeRef.reference.Scratch) :=
 OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)
def padded (nodes : Slice U8) (capacity : Nat) (s : MultiproofConeRef.reference.Scratch) :=
 MultiproofConePadding.scan (4*(capacity-count s))
  ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*count s))

def run (H : Bytes → State) (root : Root) (batch kind : Nat)
 (nodes : Slice U8) (s : MultiproofConeRef.reference.Scratch) : List Event × Answer :=
 let capacity := OraclePortSelectedDraft.capacity (3*batch+kind)
 if ¬OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s) then
  ([.missingCount],(.Err .Merkle,s.idx,s.val))
 else if count s>capacity then
  ([.capacity nodes (count s)],(.Err .Parse,s.idx,s.val))
 else if padded nodes capacity s=false then
  ([.padding nodes (count s)],(.Err .Parse,s.idx,s.val))
 else
  let physical := MultiproofConeSlotTail.prefixNodes nodes (count s)
  let entry := NNH_MerkleLevelsExecute.entry
   (NJP_RequestTransport.hash (MultiproofConePhysicalTransport.rawOracle H)) root physical
   (NJV_EntryABI.initial s.idx s.val s.n)
  ([.verify nodes (count s) s entry.1 entry.2],
   ((if entry.2.1 then .Ok () else .Err .Merkle),
    (NJP_ScratchCarrier.emitted entry.2.2).idx,(NJP_ScratchCarrier.emitted entry.2.2).val))

theorem native (H : Bytes → State) (root : Root) (batch kind : Nat)
 (nodes : Slice U8) (s : MultiproofConeRef.reference.Scratch) :
 Terminal H root batch kind nodes s (run H root batch kind nodes s).1
  (run H root batch kind nodes s).2 := by
 unfold run
 split
 · rename_i bad
   exact .missing bad
 · rename_i well
   have well := Classical.not_not.mp well
   split
   · rename_i excess
     exact .capacity well excess
   · rename_i fits
     have fits : count s ≤ OraclePortSelectedDraft.capacity (3*batch+kind) := by omega
     split
     · rename_i bad
       exact .padding well fits bad
     · rename_i good
       have good : padded nodes (OraclePortSelectedDraft.capacity (3*batch+kind)) s=true :=
        Bool.eq_true_of_not_eq_false good
       exact .verify well fits good _ _ (NNH_MerkleLevelsExecute.entry_native _ _ _ _)
#print axioms native
end AspisR1.NNH_MerkleTerminalExecute
