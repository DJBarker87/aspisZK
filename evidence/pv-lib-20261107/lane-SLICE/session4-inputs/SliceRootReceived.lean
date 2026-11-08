import PV_STX2_SliceRootClone
set_option autoImplicit false
noncomputable section
namespace PV_STX2_SliceRootReceived
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax PV_STX2_SliceMachine PV_STX2_SliceRootTransport
open PV_STX2_SliceRootComplete PV_STX2_SliceRootClone
open PV_STX2_SliceClonePointers PV_STX2_SliceCloneParts

/-- Conditional on owner acceptance of the translator patch. Exact successful
allocator-reply store after the five source lifetimes in the transported run. -/
def successStore (value : ProverRwFull.aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (replacement alloc : Data) : Store Data :=
  PV_STX2_SliceCloneLifetimes.prepared
    (PV_STX2_SliceCloneLifetimes.replied (prepared value replacement) 12 0 alloc) 12

/-- Conditional on owner acceptance of the translator patch. Retain every full
native allocator reply from the transported original entry, by reply1 and
allocator_reply BY NAME. The complete received classification preserves pending,
fail/div/fault, exact post-worlds/events and every original suspended caller. -/
theorem received113 {W E : Type} (base : Carrier W Data) (control : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (value : ProverRwFull.aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (replacement : Data) (w : W) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch (wholeHandler handler) 113
      ⟨.running (config (PV_STX2_SliceTypedEntry.entry value) replacement),w,[]⟩ =
    PV_STX2_SliceAllocatorCall.received (prepared value replacement)
      (clone value replacement).callers 12 0
      (handler (PV_STX2_SliceAllocatorCall.request (prepared value replacement) 0) w) := by
  rw [PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 112 1,allocator112]
  unfold PV_STX2_SliceClonePointers.carrier
  rw [PV_STX2_SliceAllocatorCall.reply1,allocator_reply]

/-- Conditional on owner acceptance of the translator patch. Reuse the named
reply_then5 law after transported112. Success is ONLY this actual full reply
branch; received113 retains all other branches. No descriptor read success or
allocation ownership follows from reaching this source instruction cut. -/
theorem initialized118 {W E : Type} (base : Carrier W Data) (control : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (value : ProverRwFull.aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (replacement : Data) (w post : W) (alloc : Data) (events : List E)
    (reply : handler (PV_STX2_SliceAllocatorCall.request (prepared value replacement) 0) w =
      ⟨.returned (.ok alloc),post,events⟩) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch (wholeHandler handler) 118
      ⟨.running (config (PV_STX2_SliceTypedEntry.entry value) replacement),w,[]⟩ =
    ⟨.running ⟨{activation := 12,remaining := PV_STX2_SliceF13.program.body.drop 10},
      (clone value replacement).callers,successStore value replacement alloc⟩,post,events⟩ := by
  rw [PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 112 6,allocator112]
  apply PV_STX2_SliceCloneLifetimes.reply_then5 (pointers base)
  rw [allocator_reply,reply]

/-- Conditional on owner acceptance of the translator patch. The transported
source store's next activation remains14, derived from clone_facts and f20's
single call. It is not a supplied child activation or a claim that f21 is reached. -/
theorem counter (value : ProverRwFull.aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (replacement alloc : Data) : (successStore value replacement alloc).nextActivation = 14 := by
  have h : (prepared value replacement).nextActivation = 13 := (facts value replacement).2.1
  simp [successStore,PV_STX2_SliceCloneLifetimes.prepared,
    PV_STX2_SliceCloneLifetimes.replied,PV_STX2_SliceAllocatorCall.called,
    PV_STX2_SliceAllocatorCall.entered,PV_STX2_Native.arguments,write,h]

/-- Conditional on owner acceptance of the translator patch. The SAME backing
root survives the actual reply/lifetimes; no native Vec header is fabricated,
read from a pure column array, or supplied as a desired OWNER equality. -/
theorem backing (value : ProverRwFull.aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (replacement alloc : Data) :
    (successStore value replacement alloc).cells ⟨0,0,[]⟩ = some replacement := by
  have p : (prepared value replacement).cells ⟨0,0,[]⟩ = some replacement := by
    unfold PV_STX2_SliceRootClone.prepared
    rw [(PV_STX2_SliceEntryPreservation.allocator_cells
      (clone value replacement).store 12 0 ⟨0,0,[]⟩ (by decide)).1]
    exact PV_STX2_SliceRootClone.backing value replacement
  have n : (prepared value replacement).nextActivation = 13 := (facts value replacement).2.1
  have c := (PV_STX2_SliceEntryPreservation.allocator_call_cells
    (prepared value replacement) 12 0 ⟨0,0,[]⟩ (by decide)
    (by change 0 ≠ (prepared value replacement).nextActivation; rw [n]; decide)).1
  unfold successStore
  rw [PV_STX2_SliceCloneLifetimes.other_cells _ _ _ (by decide)]
  simp only [PV_STX2_SliceCloneLifetimes.replied,PV_STX2_SliceAllocatorCall.called]
  simp only [write,n]
  simpa only [if_neg (by decide : (⟨0,0,[]⟩ : Address) ≠ ⟨12,2,[]⟩),
    if_neg (by decide : (⟨0,0,[]⟩ : Address) ≠ ⟨13,0,[]⟩)] using c.trans p

#print axioms successStore
#print axioms received113
#print axioms initialized118
#print axioms counter
#print axioms backing
end PV_STX2_SliceRootReceived
