import NKV_TreeModel
import NKV_QueryPlan
import NKV_VerifyInvocation
import NKV_AbortPrefix
set_option autoImplicit false
noncomputable section
namespace NLL
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Indices := NKV_StepErasure.Indices
abbrev Values := NKV_StepErasure.Values
abbrev Root := Array U8 32#usize
abbrev Keys := Array U64 16#usize
abbrev Reply := core.result.Result Unit verifier.Error
abbrev Answer := Reply × Indices × Values
abbrev History := List (Bytes × State)

/-- One parent frame, retained through entry, each leaf, and the terminal cut.
The input proof/queries/root are immutable context, not independently rebuilt
child inputs. Both complete scratch arrays are in this state. -/
structure Frame where
 keys : Keys
 scratch : reference.Scratch
 position : Usize

/-- Source-order cut events. Scalar-only cuts remain visible; digest histories
are attached only to the leaf or verifier occurrence that actually issued them.
No event means a call was made merely because it occurs in the frozen source. -/
inductive Event where
 | entry (lo n slot : Usize) (keys : Keys)
 | leaf (position : Usize) (key : U64) (opening : Slice U8) (digest : Root)
 | missingCount
 | capacity (nodes : Slice U8) (count : Nat)
 | padding (nodes : Slice U8) (count : Nat)
 | verify (nodes : Slice U8) (count : Nat) (before : reference.Scratch)
     (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest))
     (out : Bool × NJP_RowModel.Scratch)

/-- Erase scalar observations without sorting, deduplicating, or inventing
queries. This is a cut projection, not an endpoint premise. -/
def history : List Event → History
 | [] => []
 | .entry _ _ _ _ :: rest => history rest
 | .leaf _ _ view digest :: rest =>
   -- The tree index is supplied by the contextual projection below.
   history rest
 | .missingCount :: rest => history rest
 | .capacity _ _ :: rest => history rest
 | .padding _ _ :: rest => history rest
 | .verify _ _ _ queries _ :: rest => NJV_AdoptedObservation.history queries ++ history rest

def leafHistory (kind : Usize) (events : List Event) : History :=
 events.flatMap (fun e => match e with
 | .leaf _ _ view digest => [(AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input kind view),
     AspisV8R19.SqueezeOracleBridge.decodeState digest)]
 | .verify _ _ _ queries _ => NJV_AdoptedObservation.history queries
 | _ => [])

/-- Returning native terminal cut. Each constructor is one actual exit;
verify keeps the CLOSED child's full footprint at exactly the entered call.
The count/padding scalar replies use the pinned std/closed mathematical law,
whose SAME-input instantiation is proved in the terminal step modules. -/
inductive Terminal (H : Bytes → State) (root : Root) (batch kind : Nat)
 (nodes : Slice U8) (s : reference.Scratch) : List Event → Answer → Prop where
 | missing (bad : ¬OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s)) :
   Terminal H root batch kind nodes s [.missingCount] (.Err .Merkle,s.idx,s.val)
 | capacity (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s))
   (excess : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)>
     OraclePortSelectedDraft.capacity (3*batch+kind)) :
   Terminal H root batch kind nodes s [.capacity nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))]
     (.Err .Parse,s.idx,s.val)
 | padding (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s))
   (fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤OraclePortSelectedDraft.capacity (3*batch+kind))
   (bad : MultiproofConePadding.scan
     (4*(OraclePortSelectedDraft.capacity (3*batch+kind)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
     ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))=false) :
   Terminal H root batch kind nodes s [.padding nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))]
     (.Err .Parse,s.idx,s.val)
 | verify (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s))
   (fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤OraclePortSelectedDraft.capacity (3*batch+kind))
   (padding : MultiproofConePadding.scan
     (4*(OraclePortSelectedDraft.capacity (3*batch+kind)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
     ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))=true)
   (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
   (child : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (MultiproofConePhysicalTransport.rawOracle H)) root
     (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
     (NJV_EntryABI.initial s.idx s.val s.n) queries out) :
   Terminal H root batch kind nodes s
     [.verify nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)) s queries out]
     ((if out.1 then .Ok () else .Err .Merkle),(NJP_ScratchCarrier.emitted out.2).idx,
       (NJP_ScratchCarrier.emitted out.2).val)
end NLL
end
