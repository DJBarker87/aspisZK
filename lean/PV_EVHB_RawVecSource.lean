import PV_EVHB_RawVecOwner
import PV_EVH_Runtime
/-! Source-shaped RawVec control flow with explicit source owner slots. The
allocator primitives retain full native outcomes/worlds/events. Their actual
Global/System interpretation and the original callers' receiver-to-slot map
are not supplied by this module. No whole-operation compatibility law is a
field of Runtime. This module is not an installation at the deployed entry. -/
set_option autoImplicit false
namespace PV_EVHB_RawVecSource
open Aeneas Aeneas.Std R1Z.PV_FXM_ReserveWorld PV_EVHB_RawVecOwner

abbrev ReserveError := R1Z.PV_FXM_ReserveWorld.Error

structure Run (S F A : Type) where
  outcome : PV_EVH_Runtime.Outcome A
  world : NativeWorld S F
  events : List PV_RJ4IDB.NativeEvent

abbrev Q (S F A : Type) := NativeWorld S F → Run S F A

def lift {S F A : Type} (r : Result A) : Q S F A := fun w => ⟨.returned r,w,[]⟩

def bind {S F A B : Type} (m : Q S F A) (k : A → Q S F B) : Q S F B := fun w =>
  let r := m w
  match r.outcome with
  | .returned (.ok a) =>
    let s := k a r.world
    ⟨s.outcome,s.world,r.events ++ s.events⟩
  | .returned (.fail e) => ⟨.returned (.fail e),r.world,r.events⟩
  | .returned .div => ⟨.returned .div,r.world,r.events⟩
  | .fault e => ⟨.fault e,r.world,r.events⟩
  | .exhausted => ⟨.exhausted,r.world,r.events⟩

structure Runtime (S F : Type) where
  allocate : Header → Nat → Q S F (Except Unit Nat)
  grow : Header → Nat → Q S F (Except Unit Nat)
  shrink : Header → Nat → Q S F (Except Unit Nat)
  deallocate : Header → Q S F Unit
  capacityOverflow : Q S F Empty
  handleAllocError : core.alloc.layout.Layout → Q S F Empty

def handleError {S F : Type} (runtime : Runtime S F) : ReserveError → Q S F Empty
  | .capacityOverflow => runtime.capacityOverflow
  | .allocError layout => runtime.handleAllocError layout

def capacity (wordMax : Nat) (h : Header) : Nat :=
  if h.shape.width=0 then wordMax else h.cap

/-- Under source validity len≤capacity, Rust's wrapping subtraction has this
natural-number value. No wrapping-subtraction equivalence is claimed outside
that domain. -/
def needsToGrow (wordMax : Nat) (h : Header) (additional : Nat) : Prop :=
  additional > capacity wordMax h - h.len

def allocError (h : Header) (cap : Nat) : ReserveError :=
  .allocError ⟨usize (cap*h.shape.width),h.shape.align⟩

def allocationCall {S F : Type} (runtime : Runtime S F) (h : Header) (cap : Nat) :
    Q S F (Except Unit Nat) :=
  if h.shape.width=0 ∨ h.cap=0 then runtime.allocate h cap else runtime.grow h cap

def mappedAnswer (h : Header) (cap : Nat) : Except Unit Nat → Except ReserveError Nat
  | .ok pointer => .ok pointer
  | .error _ => .error (allocError h cap)

def finishGrow {S F : Type} (runtime : Runtime S F) (byteMax : Nat)
    (h : Header) (cap : Nat) : Q S F (Except ReserveError Nat) :=
  if cap*h.shape.width > byteMax then lift (.ok (.error .capacityOverflow))
  else
    bind (allocationCall runtime h cap) fun answer => lift (.ok (mappedAnswer h cap answer))

def commit {S F : Type} (owner : Nat) (h : Header) (cap : Nat)
    (answer : Except ReserveError Nat) : Q S F (Except ReserveError Unit) := fun w =>
  match answer with
  | .error error => ⟨.returned (.ok (.error error)),w,[]⟩
  | .ok pointer => ⟨.returned (.ok (.ok ())),install w owner h pointer cap,[]⟩

def growExact {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) : Q S F (Except ReserveError Unit) :=
  if h.shape.width=0 then lift (.ok (.error .capacityOverflow))
  else if h.len+additional>wordMax then lift (.ok (.error .capacityOverflow))
  else bind (finishGrow runtime byteMax h (h.len+additional))
    (commit owner h (h.len+additional))

def minCap (size : Nat) : Nat := if size=1 then 8 else if size≤1024 then 4 else 1

def growAmortized {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (len additional : Nat) : Q S F (Except ReserveError Unit) :=
  if h.shape.width=0 then lift (.ok (.error .capacityOverflow))
  else if len+additional>wordMax then lift (.ok (.error .capacityOverflow))
  else
    let cap := max (minCap h.shape.width) (max (h.cap*2) (len+additional))
    bind (finishGrow runtime byteMax h cap) (commit owner h cap)

def tryReserveExact {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) : Q S F (Except ReserveError Unit) :=
  if additional > capacity wordMax h - h.len then
    growExact runtime wordMax byteMax owner h additional
  else lift (.ok (.ok ()))

def tryReserve {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) : Q S F (Except ReserveError Unit) :=
  if additional > capacity wordMax h - h.len then
    growAmortized runtime wordMax byteMax owner h h.len additional
  else lift (.ok (.ok ()))

def handle {S F : Type} (runtime : Runtime S F)
    (action : Q S F (Except ReserveError Unit)) : Q S F Unit :=
  bind action fun answer => match answer with
  | .ok () => lift (.ok ())
  | .error error => bind (handleError runtime error) Empty.elim

def reserve {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) : Q S F Unit :=
  handle runtime (tryReserve runtime wordMax byteMax owner h additional)

def reserveExact {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) : Q S F Unit :=
  handle runtime (tryReserveExact runtime wordMax byteMax owner h additional)

def growOne {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) : Q S F Unit :=
  handle runtime (growAmortized runtime wordMax byteMax owner h h.cap 1)

def drop {S F : Type} (runtime : Runtime S F) (h : Header) : Q S F Unit :=
  if h.shape.width=0 ∨ h.cap=0 then lift (.ok ()) else runtime.deallocate h

theorem growing_layout_changes (h : Header) (cap : Nat)
    (sized : 0<h.shape.width) (grows : h.cap<cap) :
    layout h cap ≠ layout h h.cap := by
  intro equal
  exact (Nat.ne_of_gt (Nat.mul_lt_mul_of_pos_right grows sized))
    (congrArg Allocation.bytes equal)

theorem finish_transfers_old_ownership {S F : Type} (w : NativeWorld S F) (h : Header)
    (pointer cap : Nat) (backend : S) (nonzero : h.cap≠0)
    (sized : 0<h.shape.width) (grows : h.cap<cap) :
    ¬ Owned (allocated w h pointer cap backend) h := by
  by_cases same : h.pointer=pointer
  · subst pointer
    exact inplace_finish_grow_not_owned w h cap backend nonzero
      (growing_layout_changes h cap sized grows)
  · exact moving_finish_grow_not_owned w h pointer cap backend nonzero same

theorem bind_fail {S F A B : Type} (m : Q S F A) (k : A → Q S F B)
    (w : NativeWorld S F) (error : Aeneas.Std.Error)
    (failed : (m w).outcome=.returned (.fail error)) :
    bind m k w=⟨.returned (.fail error),(m w).world,(m w).events⟩ := by
  simp only [bind,failed]

theorem bind_div {S F A B : Type} (m : Q S F A) (k : A → Q S F B)
    (w : NativeWorld S F) (diverged : (m w).outcome=.returned .div) :
    bind m k w=⟨.returned .div,(m w).world,(m w).events⟩ := by
  simp only [bind,diverged]

theorem bind_fault {S F A B : Type} (m : Q S F A) (k : A → Q S F B)
    (w : NativeWorld S F) (error : PV_EVH_Runtime.Fault)
    (failed : (m w).outcome=.fault error) :
    bind m k w=⟨.fault error,(m w).world,(m w).events⟩ := by
  simp only [bind,failed]

theorem bind_exhausted {S F A B : Type} (m : Q S F A) (k : A → Q S F B)
    (w : NativeWorld S F) (exhausted : (m w).outcome=.exhausted) :
    bind m k w=⟨.exhausted,(m w).world,(m w).events⟩ := by
  simp only [bind,exhausted]

theorem commit_error {S F : Type} (w : NativeWorld S F) (owner : Nat)
    (h : Header) (cap : Nat) (error : ReserveError) :
    commit owner h cap (.error error) w=⟨.returned (.ok (.error error)),w,[]⟩ := rfl

theorem commit_owned {S F : Type} (w : NativeWorld S F) (owner : Nat)
    (h : Header) (cap pointer : Nat) (pending : Pending w h pointer cap) :
    OwnedAt (commit owner h cap (.ok pointer) w).world owner :=
  pending_install w owner h pointer cap pending

theorem exact_zero {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) (zero : h.shape.width=0) :
    growExact runtime wordMax byteMax owner h additional=lift (.ok (.error .capacityOverflow)) := by
  simp only [growExact,zero,ite_true]

theorem exact_add_overflow {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) (sized : h.shape.width≠0)
    (overflow : h.len+additional>wordMax) :
    growExact runtime wordMax byteMax owner h additional=lift (.ok (.error .capacityOverflow)) := by
  simp only [growExact,if_neg sized,if_pos overflow]

theorem finish_layout_overflow {S F : Type} (runtime : Runtime S F) (byteMax : Nat)
    (h : Header) (cap : Nat) (overflow : cap*h.shape.width>byteMax) :
    finishGrow runtime byteMax h cap=lift (.ok (.error .capacityOverflow)) := by
  simp only [finishGrow,if_pos overflow]

theorem reserve_no_growth {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat)
    (room : additional≤capacity wordMax h-h.len) :
    tryReserveExact runtime wordMax byteMax owner h additional=lift (.ok (.ok ())) ∧
    tryReserve runtime wordMax byteMax owner h additional=lift (.ok (.ok ())) := by
  simp only [tryReserveExact,tryReserve,if_neg (Nat.not_lt.mpr room)]
  exact ⟨rfl,rfl⟩

/-- A returning allocator answer is mapped without replacing its post-world
or its ordered native events. This is an implication about a primitive answer,
not an assumed whole-reserve result. -/
theorem finish_return {S F : Type} (runtime : Runtime S F) (byteMax : Nat)
    (h : Header) (cap : Nat) (w post : NativeWorld S F)
    (events : List PV_RJ4IDB.NativeEvent) (answer : Except Unit Nat)
    (bounded : ¬ cap*h.shape.width>byteMax)
    (reply : allocationCall runtime h cap w=⟨.returned (.ok answer),post,events⟩) :
    finishGrow runtime byteMax h cap w=
      ⟨.returned (.ok (mappedAnswer h cap answer)),post,events⟩ := by
  simp only [finishGrow,if_neg bounded,bind,reply,lift,List.append_nil]

theorem exact_success {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional pointer : Nat) (w post : NativeWorld S F)
    (events : List PV_RJ4IDB.NativeEvent) (sized : h.shape.width≠0)
    (addBound : ¬ h.len+additional>wordMax)
    (byteBound : ¬ (h.len+additional)*h.shape.width>byteMax)
    (reply : allocationCall runtime h (h.len+additional) w=
      ⟨.returned (.ok (.ok pointer)),post,events⟩) :
    growExact runtime wordMax byteMax owner h additional w=
      ⟨.returned (.ok (.ok ())),install post owner h pointer (h.len+additional),events⟩ := by
  have finished := finish_return runtime byteMax h (h.len+additional) w post events
    (.ok pointer) byteBound reply
  simp only [growExact,if_neg sized,if_neg addBound,bind,finished,mappedAnswer,
    commit,List.append_nil]

theorem exact_denied {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) (w post : NativeWorld S F)
    (events : List PV_RJ4IDB.NativeEvent) (sized : h.shape.width≠0)
    (addBound : ¬ h.len+additional>wordMax)
    (byteBound : ¬ (h.len+additional)*h.shape.width>byteMax)
    (reply : allocationCall runtime h (h.len+additional) w=
      ⟨.returned (.ok (.error ())),post,events⟩) :
    growExact runtime wordMax byteMax owner h additional w=
      ⟨.returned (.ok (.error (allocError h (h.len+additional)))),post,events⟩ := by
  have finished := finish_return runtime byteMax h (h.len+additional) w post events
    (.error ()) byteBound reply
  simp only [growExact,if_neg sized,if_neg addBound,bind,finished,mappedAnswer,
    commit,List.append_nil]

theorem exact_success_owned {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional pointer : Nat) (w post : NativeWorld S F)
    (events : List PV_RJ4IDB.NativeEvent) (sized : h.shape.width≠0)
    (addBound : ¬ h.len+additional>wordMax)
    (byteBound : ¬ (h.len+additional)*h.shape.width>byteMax)
    (reply : allocationCall runtime h (h.len+additional) w=
      ⟨.returned (.ok (.ok pointer)),post,events⟩)
    (pending : Pending post h pointer (h.len+additional)) :
    OwnedAt (growExact runtime wordMax byteMax owner h additional w).world owner := by
  rw [exact_success runtime wordMax byteMax owner h additional pointer w post events
    sized addBound byteBound reply]
  exact pending_install post owner h pointer (h.len+additional) pending

theorem exact_denied_owned {S F : Type} (runtime : Runtime S F) (wordMax byteMax : Nat)
    (owner : Nat) (h : Header) (additional : Nat) (w : NativeWorld S F) (backend : S)
    (events : List PV_RJ4IDB.NativeEvent) (sized : h.shape.width≠0)
    (addBound : ¬ h.len+additional>wordMax)
    (byteBound : ¬ (h.len+additional)*h.shape.width>byteMax)
    (reply : allocationCall runtime h (h.len+additional) w=
      ⟨.returned (.ok (.error ())),denied w h (h.len+additional) backend,events⟩)
    (selected : lookup w owner=some h) (owned : Owned w h) :
    OwnedAt (growExact runtime wordMax byteMax owner h additional w).world owner := by
  rw [exact_denied runtime wordMax byteMax owner h additional w
    (denied w h (h.len+additional) backend) events sized addBound byteBound reply]
  exact ⟨h,selected,(denied_owned w h h (h.len+additional) backend).mpr owned⟩

theorem handle_inner_error {S F : Type} (runtime : Runtime S F)
    (action : Q S F (Except ReserveError Unit)) (w post : NativeWorld S F)
    (events : List PV_RJ4IDB.NativeEvent) (error : ReserveError)
    (reply : action w=⟨.returned (.ok (.error error)),post,events⟩) :
    handle runtime action w=
      let next := bind (handleError runtime error) Empty.elim post
      ⟨next.outcome,next.world,events++next.events⟩ := by
  simp only [handle,bind,reply]

#print axioms bind_fail
#print axioms growing_layout_changes
#print axioms finish_transfers_old_ownership
#print axioms bind_div
#print axioms bind_fault
#print axioms bind_exhausted
#print axioms commit_error
#print axioms commit_owned
#print axioms exact_zero
#print axioms exact_add_overflow
#print axioms finish_layout_overflow
#print axioms reserve_no_growth
#print axioms finish_return
#print axioms exact_success
#print axioms exact_denied
#print axioms exact_success_owned
#print axioms exact_denied_owned
#print axioms handle_inner_error
end PV_EVHB_RawVecSource
