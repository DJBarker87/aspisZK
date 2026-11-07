import PV_FN_THREAD_f6Provider126NativeJoin
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider126CallJoin
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces
abbrev Backend := PV_W1_OwnerNativeFrame.Backend

/-- The actual f6 pending call enters CLOSED126 in ONE original-interpreter
transition. No126 instruction is executed here; both saved stacks and the
source-issued store are identical to the provider entry. -/
theorem enter {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (site : PV_FN_THREAD_f6DerefInterfaces.Site) (t : Store Data) (a : Nat)
    (parents : List Frame) (saved : List LoopFrame) (w : OWNER) (es : List E)
    (stack : List Config) :
    let y := PV_FN_THREAD_f6DerefInterfaces.input site t a parents saved w es stack
    let x := PV_FN_THREAD_f6Provider126Entry.convert C b K P H y
    PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_FN_THREAD_f126_ReturnedStage.programs x) (PV_FN_THREAD_f126.installed x H ⟨a,2,[0]⟩).H 1
      ⟨⟨.running (PV_FN_THREAD_f6DerefInterfaces.caller site t a parents saved),w,es⟩,stack⟩ =
      PV_FN_THREAD_f126_Arbitrary.entry x := by
  let y := PV_FN_THREAD_f6DerefInterfaces.input site t a parents saved w es stack
  let x := PV_FN_THREAD_f6Provider126Entry.convert C b K P H y
  let M : Machine E := ⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,
    PV_FN_THREAD_f126_ReturnedStage.programs x,(PV_FN_THREAD_f126.installed x H ⟨a,2,[0]⟩).H⟩
  change PV_THR2_IntrinsicState.advance M.carrier M.control M.programs M.handler 1 _ = _
  rw [PV_FN_THREAD_f6Provider126Entry.same_entry C b K P H y (by rfl)]
  have own := PV_FN_THREAD_f6InterfaceSites.one_enter M
    (PV_FN_THREAD_f6DerefInterfaces.preStore site t a) a parents
    (PV_FN_THREAD_f6DerefInterfaces.loops site saved)
    (PV_FN_THREAD_f6DerefInterfaces.rest site) (PV_FN_THREAD_f6DerefInterfaces.fn site)
    (PV_STX2_TypedReferences.reference ⟨a,2,[0]⟩ .null)
    (PV_FN_THREAD_f6DerefInterfaces.dest site) PV_THR2_F126.live w es stack
    (by cases site <;> rfl) (by cases site <;> rfl)
  convert own using 1 <;> cases site <;> rfl

/-- Prepend the concrete source call-entry step to a provider reached outcome.
This keeps its exact full Post store, frame and OWNER invariant. The machine
is explicitly the provider's installed source interpreter; transport to a
single global f6 interpreter is NOT inferred from this local call join. -/
theorem prepend {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (site : PV_FN_THREAD_f6DerefInterfaces.Site) (t : Store Data) (a : Nat)
    (parents : List Frame) (saved : List LoopFrame) (w : OWNER) (es : List E)
    (stack : List Config) (out : PV_THR2_IntrinsicState.State OWNER E)
    (reached :
      let x := PV_FN_THREAD_f6Provider126Entry.convert C b K P H
        (PV_FN_THREAD_f6DerefInterfaces.input site t a parents saved w es stack)
      PV_FN_THREAD_f126.Reached x H ⟨a,2,[0]⟩ out) :
    let x := PV_FN_THREAD_f6Provider126Entry.convert C b K P H
      (PV_FN_THREAD_f6DerefInterfaces.input site t a parents saved w es stack)
    (∃ n, PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_FN_THREAD_f126_ReturnedStage.programs x) (PV_FN_THREAD_f126.installed x H ⟨a,2,[0]⟩).H (1+n)
      ⟨⟨.running (PV_FN_THREAD_f6DerefInterfaces.caller site t a parents saved),w,es⟩,stack⟩ = out) ∧
    PV_FN_THREAD_f126.Frame x out ∧
    PV_W1_OwnerWellFormed.OwnerWellFormed out.current.world
      (PV_W1_LeafBoundary.statusStore out.current.status).nextActivation := by
  rcases reached with ⟨⟨n,run⟩,frame,owner⟩
  refine ⟨⟨n,?_⟩,frame,owner⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,enter C b K P H site t a parents saved w es stack]
  exact run

/-- Exhaustive outcome selection of CLOSED126 at2097,2306 and2659 from the
actual pending source call. Every non-Ok branch keeps its provider frontier;
Ok keeps the full actual return store and value. No callee contract hypothesis
or returned-case premise is introduced. This is an endpoint call join only. -/
theorem outcomes {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (site : PV_FN_THREAD_f6DerefInterfaces.Site) (t : Store Data) (a : Nat)
    (parents : List Frame) (saved : List LoopFrame) (w : OWNER) (es : List E)
    (stack : List Config) (p : Address)
    (live : a < t.nextActivation) (owner : OwnerWellFormed w t.nextActivation)
    (root : At (PV_THR2_OwnInitExactReturnedCases.carrier C b) t ⟨a,2,[0]⟩
      (PV_FN_THREAD_f222_EntryOwned.root p)) :
    let x := PV_FN_THREAD_f6Provider126Entry.convert C b K P H
      (PV_FN_THREAD_f6DerefInterfaces.input site t a parents saved w es stack)
    let out := match (PV_FN_THREAD_f222.baseReply (PV_FN_THREAD_f126_ReturnedStage.childInput x ⟨a,2,[0]⟩) H).answer with
      | .returned (.ok _) => PV_FN_THREAD_f126.successOut x ⟨a,2,[0]⟩ p
      | _ => PV_FN_THREAD_f126_Other.after x H ⟨a,2,[0]⟩
    (∃ n, PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_FN_THREAD_f126_ReturnedStage.programs x) (PV_FN_THREAD_f126.installed x H ⟨a,2,[0]⟩).H (1+n)
      ⟨⟨.running (PV_FN_THREAD_f6DerefInterfaces.caller site t a parents saved),w,es⟩,stack⟩ = out) ∧
    PV_FN_THREAD_f126.Frame x out ∧
    PV_W1_OwnerWellFormed.OwnerWellFormed out.current.world
      (PV_W1_LeafBoundary.statusStore out.current.status).nextActivation := by
  let x := PV_FN_THREAD_f6Provider126Entry.convert C b K P H
    (PV_FN_THREAD_f6DerefInterfaces.input site t a parents saved w es stack)
  have post := PV_FN_THREAD_f6Provider126Entry.at_actual_sites C b K P H site t a parents saved w es stack p live owner root
  change PV_FN_THREAD_f126.Post x H ⟨a,2,[0]⟩ p at post
  have result := post.2
  dsimp only
  cases h : (PV_FN_THREAD_f222.baseReply (PV_FN_THREAD_f126_ReturnedStage.childInput x ⟨a,2,[0]⟩) H).answer with
  | pending =>
    simp only [h] at result ⊢
    exact prepend C b K P H site t a parents saved w es stack _ result
  | fault f =>
    simp only [h] at result ⊢
    exact prepend C b K P H site t a parents saved w es stack _ result
  | returned r =>
    cases r with
    | fail err =>
      simp only [h] at result ⊢
      exact prepend C b K P H site t a parents saved w es stack _ result
    | div =>
      simp only [h] at result ⊢
      exact prepend C b K P H site t a parents saved w es stack _ result
    | ok old =>
      simp only [h] at result ⊢
      exact prepend C b K P H site t a parents saved w es stack _ result.1

#print axioms enter
#print axioms prepend
#print axioms outcomes
end PV_FN_THREAD_f6Provider126CallJoin
