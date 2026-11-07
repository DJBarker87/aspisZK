import NNH_MerkleLevelsExecute
import NLL_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleTerminalFinish
open Aeneas Aeneas.Std NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def result (nodes : Slice U8) (s : MultiproofConeRef.reference.Scratch)
 (history : List (NJP_RowModel.Request × NJP_RowModel.Digest))
 (out : Bool × NJP_RowModel.Scratch) : List Event × Answer :=
 ([.verify nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)) s history out],
  ((if out.1 then .Ok () else .Err .Merkle),
   (NJP_ScratchCarrier.emitted out.2).idx,(NJP_ScratchCarrier.emitted out.2).val))

theorem native (H : Bytes → State) (root : Root) (batch kind : Nat)
 (nodes : Slice U8) (s : MultiproofConeRef.reference.Scratch)
 (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s))
 (fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s) ≤ OraclePortSelectedDraft.capacity (3*batch+kind))
 (padding : MultiproofConePadding.scan
  (4*(OraclePortSelectedDraft.capacity (3*batch+kind)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
  ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))=true)
 (history : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
 (child : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (MultiproofConePhysicalTransport.rawOracle H)) root
  (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
  (NJV_EntryABI.initial s.idx s.val s.n) history out) :
 Terminal H root batch kind nodes s (result nodes s history out).1 (result nodes s history out).2 :=
 .verify well fits padding history out child
#print axioms native
end AspisR1.NNH_MerkleTerminalFinish
