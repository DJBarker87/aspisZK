import NHB_Inactive
set_option autoImplicit false
namespace AspisR1.NHB_Observation
open Aeneas Aeneas.Std Result
open Query31ExplicitScanBody
abbrev Scan := NGQ_SamplerTrace.State
abbrev Fields := NHB_Reference.Fields

def observe (next : Scan) (x : U32) (last : Nat) (stop : Bool) (j : Fin 22) : Fields :=
 {stop:=stop,candidate:=x,cursor:=last,length:=next.accepted_len.val,
  draws:=next.draws.val,word:=NHB_Inactive.cell next.accepted j}

/-- Local six-field observations for ALL windows of the SAME native poststate.
This is not a whole sampler/Result equality, or a success premise. -/
def Relation (s next : Scan) (x : U32) (cursor last : Nat) (stop : Bool) : Prop :=
 ∀ j, observe next x last stop j=NHB_Reference.fields s x cursor j

theorem continuing_frame (s next : Scan) (x : U32) (cursor last : Nat) (stop : Bool)
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64)
    (observed : Relation s next x cursor last stop) :
    stop=false ∧ last=cursor+1 ∧
      NGQ_SamplerStep.Frame s next x
        (NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val)) := by
  let zero : Fin 22 := ⟨0,by decide⟩
  have equal := observed zero
  have stats := NHB_Reference.continuing s x cursor zero hlen hdraw
  have hs : stop=false := (congrArg NHB_Reference.Fields.stop equal).trans stats.1
  have hc : last=cursor+1 := (congrArg NHB_Reference.Fields.cursor equal).trans stats.2.1
  have hd : next.draws.val=s.draws.val+1 := (congrArg NHB_Reference.Fields.draws equal).trans stats.2.2.1
  have hn : next.accepted_len.val=s.accepted_len.val+
      (if NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val) then 0 else 1) :=
    (congrArg NHB_Reference.Fields.length equal).trans stats.2.2.2
  refine ⟨hs,hc,NHB_FullFrame.survivor_frame s next x _ hd hn ?_⟩
  intro j hl hr
  have bound : j<22 := by have := next.accepted.property; change next.accepted.val.length=22 at this; omega
  let index : Fin 22 := ⟨j,bound⟩
  change NHB_Inactive.cell next.accepted index =
    NHB_Inactive.cell (if NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val)
      then s.accepted else s.accepted.set s.accepted_len x) index
  clear hl hr
  have cell := congrArg NHB_Reference.Fields.word (observed index)
  have notfull : ¬(s.accepted_len.val=22 ∨ s.draws.val=64) := by omega
  have halt : decide (s.accepted_len.val=22 ∨ s.draws.val=64)=false := by simp only [notfull,decide_false]
  cases member : NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val) with
  | true =>
    simp [NHB_Reference.fields,halt,member,observe] at cell
    simpa only [member,if_true,NHB_Inactive.cell] using cell
  | false =>
    simp [NHB_Reference.fields,halt,member,observe] at cell
    have update := NHB_Reference.set_window s x index
    simpa only [member,Bool.false_eq_true,if_false,NHB_Inactive.cell] using cell.trans update.symm

theorem stopped_state (s next : Scan) (x : U32) (cursor last : Nat) (stop : Bool)
    (full : s.accepted_len.val=22 ∨ s.draws.val=64)
    (observed : Relation s next x cursor last stop) :
    stop=true ∧ last=cursor+1 ∧ next=s := by
  let zero : Fin 22 := ⟨0,by decide⟩
  have equal := observed zero
  have stats := NHB_Reference.stopped s x cursor zero full
  have hs : stop=true := (congrArg NHB_Reference.Fields.stop equal).trans stats.1
  have hc : last=cursor+1 := (congrArg NHB_Reference.Fields.cursor equal).trans stats.2.1
  have hn : next.accepted_len=s.accepted_len := UScalar.eq_of_val_eq
    ((congrArg NHB_Reference.Fields.length equal).trans stats.2.2.1)
  have hd : next.draws=s.draws := UScalar.eq_of_val_eq
    ((congrArg NHB_Reference.Fields.draws equal).trans stats.2.2.2.1)
  have ha : next.accepted=s.accepted := by
    apply NHB_FullFrame.array_ext
    intro j hl hr
    have bound : j<22 := by have := next.accepted.property; change next.accepted.val.length=22 at this; omega
    let index : Fin 22 := ⟨j,bound⟩
    have cell := congrArg NHB_Reference.Fields.word (observed index)
    have word := (NHB_Reference.stopped s x cursor index full).2.2.2.2
    exact cell.trans word
  refine ⟨hs,hc,?_⟩
  cases next
  cases s
  cases ha
  cases hn
  cases hd
  rfl

/-- The extra scalar pre-observations used to avoid array snapshots are always
available from a prestate. They add no restriction on source executions. -/
theorem ghost_inputs (s : Scan) (x : U32) (j : Fin 22) :
    ∃ old : U32, ∃ member : Bool,
      old=NHB_Inactive.cell s.accepted j ∧
      member=NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val) :=
  ⟨_,_,rfl,rfl⟩

#print axioms continuing_frame
#print axioms stopped_state
#print axioms ghost_inputs
end AspisR1.NHB_Observation
