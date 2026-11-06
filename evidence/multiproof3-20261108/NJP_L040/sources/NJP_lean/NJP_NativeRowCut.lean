import NJP_WriteCarrier

set_option autoImplicit false
noncomputable section
namespace NJP_NativeRowCut
open Aeneas Aeneas.Std Result NJP_RowModel

structure Log where
 calls : Nat
 kind : Nat
 callIndex : Nat
 values : Fin 16 → Digest
 sibling : Digest
 left : Bool
 writeCalls : Nat
 writeIndex : Nat
 writeDigest : Digest

def observedValue (log : Log) (i : Nat) : Digest :=
 if h : i<16 then log.values ⟨i,h⟩ else fun _ => 0#u8

def request (log : Log) : Request :=
 if log.kind=1 then (observedValue log log.callIndex,observedValue log (log.callIndex+1))
 else if log.left then (observedValue log log.callIndex,log.sibling)
 else (log.sibling,observedValue log log.callIndex)

def writes (s : Scratch) (i length : Nat) : Prop :=
 i<s.n  ∧  (paired s i ∨ s.cursor+32 ≤ length)
instance (s : Scratch) (i length : Nat) : Decidable (writes s i length) := inferInstanceAs (Decidable (_  ∧  _))

def cursor (s : Scratch) (i length : Nat) : Nat :=
 if i<s.n  ∧  ¬paired s i  ∧  s.cursor+32 ≤ length then s.cursor+32 else s.cursor

def nextI (s : Scratch) (i length : Nat) : Nat :=
 if i<s.n then if paired s i then i+2 else if s.cursor+32 ≤ length then i+1 else i else i

/-- Reviewed native postconditions: K017..K022/K025..K056 returning cuts,
K060/K061 missing prefix and K062/K063 exhaustion, composed with K033..K036
real write windows over the exact KMX value laws. Every coordinate is separate
and arbitrary. Child reply is a parameter, not a success premise. Domain is
an own caller input invariant, not a conclusion hidden in this cut. -/
structure Cut (s : Scratch) (i w length : Nat) (nodes : Nat → U8) (reply : Digest)
    (after : Scratch) (ni nw : Nat) (returned : Bool) (log : Log) : Prop where
 count : log.calls=if writes s i length then 1 else 0
 kind : writes s i length → log.kind=if paired s i then 1 else 2
 inputIndex : writes s i length → log.callIndex=i
 inputValues : writes s i length → ∀ k j, log.values k j=s.values k j
 siblingValues : i<s.n → ¬paired s i → s.cursor+32 ≤ length → ∀ j, log.sibling j=nodes (s.cursor+j.val)
 orientation : i<s.n → ¬paired s i → s.cursor+32 ≤ length → log.left=decide (index s i%2=0)
 writeCount : log.writeCalls=if writes s i length then 1 else 0
 writeIndex : writes s i length → log.writeIndex=w
 writeReply : writes s i length → ∀ j, log.writeDigest j=reply j
 countFrame : after.n=s.n
 cursorValue : after.cursor=cursor s i length
 indexValues : ∀ k, after.indices k=if writes s i length  ∧  k.val=w then index s i/2 else s.indices k
 digestValues : ∀ k j, after.values k j=if writes s i length  ∧  k.val=w then reply j else s.values k j
 nextIndex : ni=nextI s i length
 nextWrite : nw=if writes s i length then w+1 else w
 returnValue : returned=decide (¬i<s.n ∨ paired s i ∨ s.cursor+32 ≤ length)

theorem arguments (s : Scratch) (i w length : Nat) (nodes : Nat → U8) (reply : Digest)
    (after : Scratch) (ni nw : Nat) (returned : Bool) (log : Log)
    (cut : Cut s i w length nodes reply after ni nw returned log) (entered : writes s i length) :
 request log=if paired s i then occupiedRequest s i else siblingRequest s i nodes := by
 have values : log.values=s.values := by funext k j;exact cut.inputValues entered k j
 have observed : observedValue log=value s := by
   funext j
   simp only [observedValue,value,values]
 by_cases both : paired s i
 · simp only [request,cut.kind entered,if_pos both,ite_true,cut.inputIndex entered,observed]
   rfl
 · have available : s.cursor+32 ≤ length := entered.2.resolve_left both
   have sibling : log.sibling=window nodes s.cursor := funext (cut.siblingValues entered.1 both available)
   simp only [request,cut.kind entered,if_neg both,show ¬(2:Nat)=1 by decide,ite_false,
     cut.inputIndex entered,observed,sibling,cut.orientation entered.1 both available,siblingRequest]
   by_cases even : index s i%2=0 <;> simp only [even,decide_true,decide_false,ite_true,ite_false]

theorem state (s : Scratch) (i w length : Nat) (nodes : Nat → U8) (reply : Digest)
    (after : Scratch) (ni nw : Nat) (returned : Bool) (log : Log)
    (cut : Cut s i w length nodes reply after ni nw returned log) :
 after=if writes s i length then write s i w (cursor s i length) reply else s := by
 by_cases entered : writes s i length
 · rw [if_pos entered]
   apply NJP_WriteCarrier.state_ext
   · funext k
     simpa only [write,entered,true_and] using cut.indexValues k
   · funext k j
     simpa only [write,entered,true_and] using cut.digestValues k j
   · exact cut.countFrame
   · exact cut.cursorValue
 · rw [if_neg entered]
   apply NJP_WriteCarrier.state_ext
   · funext k
     simpa only [entered,false_and,ite_false] using cut.indexValues k
   · funext k j
     simpa only [entered,false_and,ite_false] using cut.digestValues k j
   · exact cut.countFrame
   · have no_sibling : ¬(i<s.n  ∧  ¬paired s i  ∧  s.cursor+32 ≤ length) := by
       intro h
       exact entered ⟨h.1,Or.inr h.2.2⟩
     simpa only [cursor,if_neg no_sibling] using cut.cursorValue

#print arguments
#print axioms arguments
#print state
#print axioms state
end NJP_NativeRowCut
end
