import PV_FN_THREAD_f6ArcPostContinuation
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6CatchPre
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6InterfaceSites

/-- Source Scope construction and capture wrapping preserve the actual Arc
in Scope field0. The incoming live bound follows from124's allocation Post. -/
theorem scope_at {E : Type} (base : Carrier OWNER Data) (b : Bool)
    (post : Store Data) (a : Nat) (parents : List Frame) (arc capture : Data)
    (w : OWNER) (es : List E) (stack : List Config) (live : a < post.nextActivation) :
    let B := PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b
    At B (catchInput post a parents arc capture w es stack).store ⟨a,2,[0]⟩ arc := by
  have different : (⟨a,2,[]⟩ : Address) ≠ ⟨post.nextActivation,1,[]⟩ := by
    intro h
    exact (Nat.ne_of_lt live) (congrArg Address.activation h)
  refine ⟨PV_THR2_ScopeValue.value arc,?_,?_⟩
  · simp [catchInput,one,PV_THR2_IntrinsicFrameEnter.pending,
      PV_FN_THREAD_f6OwnContinuation.prepared,PV_THR2_ScopeValue.prepared,
      PV_THR2_ScopeCapturePrefix.prepared,PV_THR2_ScopeCaptureWrap.prepared,
      PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,different]
  · rfl

/-- No caller alias condition: the124 Post's fresh backing activation and
counter bound discharge both frame side conditions at the next call. -/
theorem arc_at {E : Type} (B : Carrier OWNER Data) (post : Store Data) (freshFrom a : Nat)
    (parents : List Frame) (arc capture payload : Data) (w : OWNER) (es : List E) (stack : List Config)
    (newArc : NewArcAt B post freshFrom arc payload) (below : a < freshFrom) :
    ArcAt B (catchInput post a parents arc capture w es stack).store arc payload := by
  rcases newArc with ⟨p,strong,weak,fresh,bounded,representation,strongOne,weakOne,root,cell,path⟩
  refine ⟨p,strong,weak,representation,root,?_,path⟩
  rw [(catch_site post a parents arc capture w es stack).2.2]
  rw [PV_FN_THREAD_f6OwnContinuation.issued_frame post a parents arc capture
    (⟨p.activation,p.localIndex,[]⟩ : Address) bounded (by
      intro h
      have above := Nat.lt_of_lt_of_le below fresh
      exact (Nat.ne_of_lt above) h.symm)]
  exact cell

/-- All substantive125 entry projections are DERIVED from124's allocation
Post and f6's own writes. Only the preceding OWNER Post remains as instrumentation
invariance; no scope/pointee/capture-alias premise is added at1989. -/
theorem after124_at1989 {E : Type} (base : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (thread_f125 : f125 (⟨PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b,K,P,H⟩ : Machine E))
    (post : Store Data) (freshFrom a : Nat) (parents : List Frame) (arc capture payload : Data)
    (w : OWNER) (es : List E) (stack : List Config)
    (newArc : NewArcAt (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      post freshFrom arc payload) (below : a < freshFrom)
    (owner : OwnerWellFormed w post.nextActivation) :
    let M : Machine E := ⟨PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b,K,P,H⟩
    let x := catchInput post a parents arc capture w es stack
    FullPost M x (fun s _ result => At M.carrier s ⟨a,2,[0]⟩ arc ∧
      ArcAt M.carrier s arc payload ∧
      (M.control.variant result = some 0 ∨ M.control.variant result = some 1)) := by
  have live : a < post.nextActivation := by
    rcases newArc with ⟨p,strong,weak,fresh,bounded,rest⟩
    exact Nat.lt_trans (Nat.lt_of_lt_of_le below fresh) bounded
  apply at1989 _ thread_f125 post a parents arc capture payload w es stack
  · apply one_valid
    · exact live
    · exact owner
  · exact scope_at base b post a parents arc capture w es stack live
  · exact arc_at _ post freshFrom a parents arc capture payload w es stack newArc below

#print axioms scope_at
#print axioms arc_at
#print axioms after124_at1989
end PV_FN_THREAD_f6CatchPre
