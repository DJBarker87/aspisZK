import CuSavingsRetainedCompositionTx1Source
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionTx1Transport
open Aeneas Aeneas.Std Result
namespace P
abbrev D := AspisR1RhoPowerTail.aspis_core.Digest32
abbrev View := AspisR1RhoPowerTail.verifier.View
abbrev Err := AspisR1RhoPowerTail.verifier.Error
end P
namespace Q
abbrev D := AspisR1RhoQuery.aspis_core.Digest32
abbrev View := AspisR1RhoQuery.verifier.View
abbrev Err := AspisR1RhoQuery.verifier.Error
end Q

def digest {H : Type} (D : P.D H) : Q.D H := ⟨D.coremarkerCopyInst,D.digest⟩
def view (v : P.View) : Q.View :=
  {variant:=v.variant,semantic:=v.semantic,y1:=v.y1,inactive:=CuSavingsRhoEntryTransport.wide v.inactive,
   round0:=v.round0,folded_root:=v.folded_root,round1:=v.round1,
   final_message:=v.final_message,query_bytes:=v.query_bytes}
def error : Q.Err → P.Err
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

def returned {T : Type} : core.result.Result T Q.Err → core.result.Result T P.Err
  | .Ok x => .Ok x
  | .Err e => .Err (error e)

variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
  [AspisR1RhoResumeCaller.ResumeCommon] [AspisR1RhoTransactions.TxCommon]

def finishOld (start len cursor : Usize) : AspisR1RhoPowerTail.Finish :=
  fun D v p a g publicValue proof k hash obs =>
    letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve
      (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    do
    let out ← AspisR1RhoTransactions.tx_old.tx1_finish (digest D) (view v)
      (CuSavingsRhoEntryTransport.prepared p) (CuSavingsRhoEntryTransport.accumulator a)
      (CuSavingsRhoEntryTransport.array CuSavingsRhoEntryTransport.wide g) publicValue proof k hash obs
    .ok (returned out)

def finishNew (start len cursor : Usize) : AspisR1RhoPowerTail.Finish :=
  fun D v p a g publicValue proof k hash obs =>
    letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve
      (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    do
    let out ← AspisR1RhoTransactions.tx_new.tx1_finish (digest D) (view v)
      (CuSavingsRhoEntryTransport.prepared p) (CuSavingsRhoEntryTransport.accumulator a)
      (CuSavingsRhoEntryTransport.array CuSavingsRhoEntryTransport.wide g) publicValue proof k hash obs
    .ok (returned out)

#print axioms digest
#print axioms view
#print axioms finishOld
#print axioms finishNew
end AspisR1.CuSavingsRetainedCompositionTx1Transport
