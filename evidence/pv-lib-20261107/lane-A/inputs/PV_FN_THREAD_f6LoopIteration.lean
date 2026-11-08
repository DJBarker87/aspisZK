import PV_FN_THREAD_f6SummaryTrace
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6LoopIteration
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6SummaryTrace

structure Context (W E : Type) where
  base : Carrier W Data
  ctl : Control
  programs : Data → Option PV_STX2_SliceSyntax.Program
  handler : PV_STX2_Native.Request Data → W → Reply W E Data
  flag : Bool
  activation : Nat
  parents : List Frame
  afterLoop : List PV_STX2_SliceSyntax.Node
  lower : List LoopFrame
  suspended : List Config

structure Cursor (W E : Type) where
  store : Store Data
  world : W
  events : List E

/-- Returned-branch DATA, not a claim that a callee returns or has this Post.
Each use below separately requires that callee's semantic Post at the actual call. -/
structure Returned (W E A : Type) where
  store : Store Data
  value : A
  world : W
  events : List E

structure Iteration (W E : Type) where
  first : Returned W E Address
  load : Returned W E Nat
  deref : Returned W E Address
  park : Returned W E Data

def loops {W E} (k : Context W E) : List LoopFrame :=
  ⟨PV_THR2_F6.block86,k.afterLoop⟩ :: k.lower

def carrier {W E} (k : Context W E) := PV_FN_THREAD_f6CounterTest.carrier k.base k.flag

def sourceState {W E} (k : Context W E) (rest : List PV_STX2_SliceSyntax.Node)
    (x : Cursor W E) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨.running ⟨{activation := k.activation,remaining := rest,loops := loops k},
    k.parents,x.store⟩,x.world,x.events⟩,k.suspended⟩

def waiting {W E} (k : Context W E) (c : Config) (x : Cursor W E) :
    PV_THR2_IntrinsicState.State W E := ⟨⟨.running c,x.world,x.events⟩,k.suspended⟩

def resumed {W E A} (x : Cursor W E) (r : Returned W E A)
    (a dest : Nat) (encode : A → Data) : Cursor W E :=
  ⟨PV_FN_THREAD_f6ReturnedContinuations.resumed r.store x.store.nextActivation
    a dest (encode r.value),r.world,x.events ++ r.events⟩

def ref (p : Address) := PV_STX2_TypedReferences.reference p .null

def firstCall {W E} (k : Context W E) (x : Cursor W E) :=
  PV_FN_THREAD_f6LoopEntry.pending x.store k.activation k.parents (loops k)
def afterFirst {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :=
  resumed x r.first k.activation 17 ref
def loadCall {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :=
  PV_FN_THREAD_f6LoadCounter.pending (afterFirst k x r).store k.activation
    k.parents (loops k) r.first.value
def afterLoad {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :=
  resumed (afterFirst k x r) r.load k.activation 15 Data.number
def beforeDeref {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) : Cursor W E :=
  let y := afterLoad k x r
  {y with store := (write (PV_FN_THREAD_f6CounterTest.prepared y.store k.activation r.load.value)
    ⟨k.activation,14,[]⟩ none)}
def derefCall {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :=
  PV_FN_THREAD_f6ParkDeref.pending (beforeDeref k x r).store k.activation k.parents (loops k)
def afterDeref {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :=
  resumed (beforeDeref k x r) r.deref k.activation 22 ref
def parkCall {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :=
  PV_FN_THREAD_f6ParkRequest.pending (afterDeref k x r).store k.activation
    k.parents (loops k) r.deref.value
def afterPark {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :=
  resumed (afterDeref k x r) r.park k.activation 20 id
def next {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) : Cursor W E :=
  let y := afterPark k x r
  {y with store := PV_FN_THREAD_f6LoopBack.prepared y.store k.activation}

/-- Four separate obligations at actual source call entries. This is not a
provider contract definition or a premise admitted at the privacy endpoint. -/
def Dependencies {W E} (C : Nat → CallPost W E) (k : Context W E)
    (x : Cursor W E) (r : Iteration W E) : Prop :=
  C 2097 (firstCall k x) x.world r.first.store
    ⟨.returned (.ok (ref r.first.value)),r.first.world,r.first.events⟩ ∧
  C 2197 (loadCall k x r) (afterFirst k x r).world r.load.store
    ⟨.returned (.ok (.number r.load.value)),r.load.world,r.load.events⟩ ∧
  C 2306 (derefCall k x r) (beforeDeref k x r).world r.deref.store
    ⟨.returned (.ok (ref r.deref.value)),r.deref.world,r.deref.events⟩ ∧
  C 2404 (parkCall k x r) (afterDeref k x r).world r.park.store
    ⟨.returned (.ok r.park.value),r.park.world,r.park.events⟩

/-- A COMPLETE nonzero own iteration: 32 own instructions and four separate
one-step call boundaries. No f126 body, prefix or final-store construction is
present. No termination bound or repeated-zero assumption is present.
The named call Post dependencies must be instantiated by provider contracts. -/
theorem iteration {W E : Type} (k : Context W E) (C : Nat → CallPost W E)
    (x : Cursor W E) (r : Iteration W E) (nonzero : r.load.value ≠ 0)
    (callee126_at2097 : C 2097 (firstCall k x) x.world r.first.store
      ⟨.returned (.ok (ref r.first.value)),r.first.world,r.first.events⟩)
    (callee127_at2197 : C 2197 (loadCall k x r) (afterFirst k x r).world r.load.store
      ⟨.returned (.ok (.number r.load.value)),r.load.world,r.load.events⟩)
    (callee126_at2306 : C 2306 (derefCall k x r) (beforeDeref k x r).world r.deref.store
      ⟨.returned (.ok (ref r.deref.value)),r.deref.world,r.deref.events⟩)
    (callee128_at2404 : C 2404 (parkCall k x r) (afterDeref k x r).world r.park.store
      ⟨.returned (.ok r.park.value),r.park.world,r.park.events⟩) :
    Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k PV_THR2_F6.block86 x) (sourceState k PV_THR2_F6.block86 (next k x r)) := by
  have e0 : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k PV_THR2_F6.block86 x) (waiting k (firstCall k x) x) := by
    apply own_eq _ _ _ _ _ 7
    rw [carrier,PV_FN_THREAD_f6OperatorCarrier.agreement]
    exact PV_FN_THREAD_f6LoopEntry.run _ k.ctl k.programs k.handler x.store
      k.activation k.parents (loops k) k.flag x.world x.events k.suspended
  have c0 : Trace (carrier k) k.ctl k.programs k.handler C
      (waiting k (firstCall k x) (x)) (sourceState k (PV_THR2_F6.block86.drop 7) (afterFirst k x r)) := by
    exact returned _ _ _ _ C 2097 (firstCall k x) _ r.first.store
      x.store.nextActivation 17 (ref r.first.value) (x).world r.first.world
      (x).events r.first.events k.suspended rfl rfl callee126_at2097
  have e1 : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k (PV_THR2_F6.block86.drop 7) (afterFirst k x r))
      (waiting k (loadCall k x r) (afterFirst k x r)) := by
    apply own_eq _ _ _ _ _ 5
    exact PV_FN_THREAD_f6ReturnedContinuations.after2097 k.base k.ctl k.programs k.handler
      r.first.store x.store.nextActivation k.activation k.parents (loops k) k.flag
      r.first.value r.first.world (x.events ++ r.first.events) k.suspended
  have c1 : Trace (carrier k) k.ctl k.programs k.handler C
      (waiting k (loadCall k x r) (afterFirst k x r)) (sourceState k (PV_THR2_F6.block86.drop 12) (afterLoad k x r)) := by
    exact returned _ _ _ _ C 2197 (loadCall k x r) _ r.load.store
      (afterFirst k x r).store.nextActivation 15 (Data.number r.load.value) (afterFirst k x r).world r.load.world
      (afterFirst k x r).events r.load.events k.suspended rfl rfl callee127_at2197
  have e2 : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k (PV_THR2_F6.block86.drop 12) (afterLoad k x r))
      (waiting k (derefCall k x r) (beforeDeref k x r)) := by
    apply own_eq _ _ _ _ _ 12
    exact PV_FN_THREAD_f6CounterNonzero.nonzero_request k.base k.ctl k.programs k.handler
      (afterLoad k x r).store k.activation r.load.value k.parents (loops k) k.flag
      (afterLoad k x r).world (afterLoad k x r).events k.suspended
      (PV_FN_THREAD_f6PostStore.destination _ _ _ _ _) nonzero
  have c2 : Trace (carrier k) k.ctl k.programs k.handler C
      (waiting k (derefCall k x r) (beforeDeref k x r)) (sourceState k (PV_THR2_F6.block86.drop 24) (afterDeref k x r)) := by
    exact returned _ _ _ _ C 2306 (derefCall k x r) _ r.deref.store
      (beforeDeref k x r).store.nextActivation 22 (ref r.deref.value) (beforeDeref k x r).world r.deref.world
      (beforeDeref k x r).events r.deref.events k.suspended rfl rfl callee126_at2306
  have e3 : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k (PV_THR2_F6.block86.drop 24) (afterDeref k x r))
      (waiting k (parkCall k x r) (afterDeref k x r)) := by
    apply own_eq _ _ _ _ _ 3
    exact PV_FN_THREAD_f6ReturnedContinuations.after2306 k.base k.ctl k.programs k.handler
      r.deref.store (beforeDeref k x r).store.nextActivation k.activation k.parents
      (loops k) k.flag r.deref.value r.deref.world
      ((beforeDeref k x r).events ++ r.deref.events) k.suspended
  have c3 : Trace (carrier k) k.ctl k.programs k.handler C
      (waiting k (parkCall k x r) (afterDeref k x r)) (sourceState k (PV_THR2_F6.block86.drop 27) (afterPark k x r)) := by
    exact returned _ _ _ _ C 2404 (parkCall k x r) _ r.park.store
      (afterDeref k x r).store.nextActivation 20 (r.park.value) (afterDeref k x r).world r.park.world
      (afterDeref k x r).events r.park.events k.suspended rfl rfl callee128_at2404
  have e4 : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k (PV_THR2_F6.block86.drop 27) (afterPark k x r))
      (sourceState k PV_THR2_F6.block86 (next k x r)) := by
    apply own_eq _ _ _ _ _ 5
    exact PV_FN_THREAD_f6LoopBack.run _ k.ctl k.programs k.handler
      (afterPark k x r).store k.activation k.parents _ k.lower
      (afterPark k x r).world (afterPark k x r).events k.suspended
  exact e0.trans (c0.trans (e1.trans (c1.trans (e2.trans (c2.trans (e3.trans (c3.trans e4)))))))

#print axioms iteration
end PV_FN_THREAD_f6LoopIteration
