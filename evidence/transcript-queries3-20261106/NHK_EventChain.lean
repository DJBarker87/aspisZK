import NHK_TraceBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHK_EventChain
open Aeneas Aeneas.Std Result CheckpointBytes5Effect NGQ_MaterializeChain
abbrev Trace := NGQ_Cuts.Trace

def walk : List Usize → Blocks → Blocks → Bytes32 → Code (Blocks × Blocks)
 | [], blocks, advances, _ => .done (blocks, advances)
 | index :: indices, blocks, advances, state => do
   let (nextBlocks, nextAdvances, nextState) ← pair index blocks advances state
   walk indices nextBlocks nextAdvances nextState

/-- Each constructor is the two chronological observations of ONE native pair.
The next receiver is exactly the advance reply just recorded. -/
inductive Observations (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    List Usize → Blocks → Blocks → Bytes32 → Blocks → Blocks → SdkC_Source.Log → Prop where
 | done (blocks advances : Blocks) (state : Bytes32) :
     Observations hashv [] blocks advances state blocks advances []
 | pair (index : Usize) (indices : List Usize) (blocks advances : Blocks)
     (state block advance : Bytes32) (finalBlocks finalAdvances : Blocks)
     (events : SdkC_Source.Log)
     (blockEdge : hashv (parts state 1#u8) = .ok block)
     (advanceEdge : hashv (parts state 2#u8) = .ok advance)
     (tail : Observations hashv indices (blocks.set index block)
       (advances.set index advance) advance finalBlocks finalAdvances events) :
     Observations hashv (index :: indices) blocks advances state
       finalBlocks finalAdvances
       (⟨parts state 1#u8,.ok block⟩ :: ⟨parts state 2#u8,.ok advance⟩ :: events)

theorem pair_trace
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (index : Usize) (blocks advances : Blocks) (state block advance : Bytes32)
    (blockEdge : hashv (parts state 1#u8) = .ok block)
    (advanceEdge : hashv (parts state 2#u8) = .ok advance) :
    Trace hashv (pair index blocks advances state)
      (.ok (blocks.set index block, advances.set index advance, advance))
      [⟨parts state 1#u8,.ok block⟩,⟨parts state 2#u8,.ok advance⟩] := by
  exact .readOk _ _ block blockEdge _ _
    (.readOk _ _ advance advanceEdge _ _ (.done _))

theorem producer
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {indices : List Usize} {blocks advances : Blocks} {state : Bytes32}
    {finalBlocks finalAdvances : Blocks} {events : SdkC_Source.Log}
    (cuts : Observations hashv indices blocks advances state finalBlocks finalAdvances events) :
    Trace hashv (walk indices blocks advances state)
      (.ok (finalBlocks,finalAdvances)) events := by
  induction cuts with
  | done blocks advances state => exact .done _
  | pair index indices blocks advances state block advance finalBlocks finalAdvances events hb ha tail ih =>
    exact NHK_TraceBind.append (pair_trace hashv index blocks advances state block advance hb ha)
      (fun v => walk indices v.1 v.2.1 v.2.2) _ events ih

theorem eight_source (state : Bytes32) :
    walk [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) state = chain state := by
  rfl

/-- Same-invocation returning pair events supply the materializer Trace.
This statement alone makes no physical origin assertion about cuts. -/
theorem eight_producer
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    (state : Bytes32) (blocks advances : Blocks) (events : SdkC_Source.Log)
    (cuts : Observations hashv
      [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) state blocks advances events) :
    Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.materializeCode state))
      (.ok (blocks, advances)) events := by
  rw [NGQ_MaterializeChain.normalized, ← eight_source]
  exact producer cuts


/-- Partial calls end the same chronological chain at that occurrence. All
earlier returned replies and the unsuccessful call itself remain in the log. -/
inductive PartialObservations
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    List Usize → Blocks → Blocks → Bytes32 → Result (Blocks × Blocks) → SdkC_Source.Log → Prop where
 | done (blocks advances : Blocks) (state : Bytes32) :
     PartialObservations hashv [] blocks advances state (.ok (blocks,advances)) []
 | blockFail (i : Usize) (indices : List Usize) (blocks advances : Blocks) (state : Bytes32)
     (error : Error) (edge : hashv (parts state 1#u8) = .fail error) :
     PartialObservations hashv (i::indices) blocks advances state (.fail error)
       [⟨parts state 1#u8,.fail error⟩]
 | blockDiv (i : Usize) (indices : List Usize) (blocks advances : Blocks) (state : Bytes32)
     (edge : hashv (parts state 1#u8) = .div) :
     PartialObservations hashv (i::indices) blocks advances state .div
       [⟨parts state 1#u8,.div⟩]
 | advanceFail (i : Usize) (indices : List Usize) (blocks advances : Blocks) (state block : Bytes32)
     (error : Error) (blockEdge : hashv (parts state 1#u8) = .ok block)
     (advanceEdge : hashv (parts state 2#u8) = .fail error) :
     PartialObservations hashv (i::indices) blocks advances state (.fail error)
       [⟨parts state 1#u8,.ok block⟩,⟨parts state 2#u8,.fail error⟩]
 | advanceDiv (i : Usize) (indices : List Usize) (blocks advances : Blocks) (state block : Bytes32)
     (blockEdge : hashv (parts state 1#u8) = .ok block)
     (advanceEdge : hashv (parts state 2#u8) = .div) :
     PartialObservations hashv (i::indices) blocks advances state .div
       [⟨parts state 1#u8,.ok block⟩,⟨parts state 2#u8,.div⟩]
 | pair (i : Usize) (indices : List Usize) (blocks advances : Blocks) (state block advance : Bytes32)
     (out : Result (Blocks × Blocks)) (events : SdkC_Source.Log)
     (blockEdge : hashv (parts state 1#u8) = .ok block)
     (advanceEdge : hashv (parts state 2#u8) = .ok advance)
     (tail : PartialObservations hashv indices (blocks.set i block)
       (advances.set i advance) advance out events) :
     PartialObservations hashv (i::indices) blocks advances state out
       (⟨parts state 1#u8,.ok block⟩ :: ⟨parts state 2#u8,.ok advance⟩ :: events)

theorem partial_producer
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {indices : List Usize} {blocks advances : Blocks} {state : Bytes32}
    {out : Result (Blocks × Blocks)} {events : SdkC_Source.Log}
    (cuts : PartialObservations hashv indices blocks advances state out events) :
    Trace hashv (walk indices blocks advances state) out events := by
  induction cuts with
  | done blocks advances state => exact .done _
  | blockFail i indices blocks advances state error edge =>
    exact .readFail _ _ error edge
  | blockDiv i indices blocks advances state edge =>
    exact .readDiv _ _ edge
  | advanceFail i indices blocks advances state block error hb ha =>
    exact .readOk _ _ block hb _ _ (.readFail _ _ error ha)
  | advanceDiv i indices blocks advances state block hb ha =>
    exact .readOk _ _ block hb _ _ (.readDiv _ _ ha)
  | pair i indices blocks advances state block advance out events hb ha tail ih =>
    exact NHK_TraceBind.append (pair_trace hashv i blocks advances state block advance hb ha)
      (fun v => walk indices v.1 v.2.1 v.2.2) _ events ih

theorem eight_partial
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    (state : Bytes32) (out : Result (Blocks × Blocks)) (events : SdkC_Source.Log)
    (cuts : PartialObservations hashv
      [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) state out events) :
    Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.materializeCode state)) out events := by
  rw [NGQ_MaterializeChain.normalized, ← eight_source]
  exact partial_producer cuts

#print axioms partial_producer
#print axioms eight_partial

#print axioms pair_trace
#print axioms producer
#print axioms eight_source
#print axioms eight_producer
end AspisR1.NHK_EventChain
end
