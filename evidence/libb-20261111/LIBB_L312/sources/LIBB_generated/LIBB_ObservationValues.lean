import LIBB_ObservationModel
set_option autoImplicit false
noncomputable section
namespace LIBB_ObservationValues
open Aeneas Aeneas.Std AspisR1
open LIBB_ObservationPieces

theorem prefix_no_write (env : RSL.Env) (e : NJU_CommonObserved.Event)
 (events : List RSL.Event) (h : Prefix env e events) (cell : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write cell bytes ∉ events := by
 obtain ⟨answered,parts,_,rfl⟩:=h
 intro member
 obtain ⟨query,_,equal⟩:=List.mem_map.mp member
 cases equal

theorem piece_no_write (env : RSL.Env) (e : NJU_CommonObserved.Event)
 (events : List RSL.Event) (h : Piece env e events) (cell : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write cell bytes ∉ events := by
 rcases h with rfl | ⟨pr,p,folded,error,_,prefixLaw⟩
 · exact LIBB_Tx2EnvTrace.no_write_event env e cell bytes
 · exact prefix_no_write env e events prefixLaw cell bytes

theorem pieces_no_write (env : RSL.Env) (source : List NJU_CommonObserved.Event)
 (events : List RSL.Event) (h : Pieces env source events) (cell : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write cell bytes ∉ events := by
 obtain ⟨pieces,relation,rfl⟩:=h
 induction relation with
 | nil => exact List.not_mem_nil
 | cons head tail ih =>
  intro member
  rcases List.mem_append.mp member with first | rest
  · exact piece_no_write env _ _ head cell bytes first
  · exact ih rest

theorem common_no_write (env : RSL.Env) (pub proof ck : Slice U8)
 (o : RSL.Obs (Except LIBB_V2Carriers.VErr Unit))
 (h : LIBB_ObservationModel.Common env pub proof ck o) (cell : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write cell bytes ∉ o.events := by
 rcases h with ⟨_,h⟩ | ⟨before,pr,p,folded,reply,suffix,prior,inside,_,priorLaw,prefixLaw,rfl⟩
 · exact pieces_no_write env _ _ h cell bytes
 · intro member
   rcases List.mem_append.mp member with first | rest
   · exact pieces_no_write env _ _ priorLaw cell bytes first
   · exact prefix_no_write env _ _ prefixLaw cell bytes rest

theorem observation_no_write (env : RSL.Env) (pub proof ck : Slice U8)
 (cell : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write cell bytes ∉ (LIBB_Tx2EnvTrace.observation env pub proof ck).events := by
 have eventsEqual : (LIBB_Tx2EnvTrace.observation env pub proof ck).events=
  LIBB_Tx2EnvTrace.events env pub proof ck := LIBB_ObservationModel.result_events _ _
 rw [eventsEqual]
 exact LIBB_Tx2EnvTrace.no_write env pub proof ck cell bytes

theorem writeFree (pub proof ck : Slice U8) :
 RSL.TAS.WriteFree (LIBB_ObservationModel.law pub proof ck) := by
 intro env o observed cell bytes
 unfold LIBB_ObservationModel.law at observed
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => rw [parsed] at observed;subst o;exact observation_no_write env pub proof ck cell bytes
 | div => rw [parsed] at observed;subst o;exact observation_no_write env pub proof ck cell bytes
 | ok reply => cases reply with
   | Err e => rw [parsed] at observed;subst o;exact observation_no_write env pub proof ck cell bytes
   | Ok v => rw [parsed] at observed;exact common_no_write env pub proof ck o observed cell bytes

/-- Exact returned-value determinism for the full law, with every stopped
prefix retained. It is deliberately distinct from whole-Obs Functional. -/
theorem returned_unique (env : RSL.Env) (pub proof ck : Slice U8)
 (o₁ o₂ : RSL.Obs (Except LIBB_V2Carriers.VErr Unit))
 (r₁ r₂ : Except LIBB_V2Carriers.VErr Unit)
 (h₁ : LIBB_ObservationModel.law pub proof ck env o₁)
 (h₂ : LIBB_ObservationModel.law pub proof ck env o₂)
 (ret₁ : o₁.exit=.ret r₁) (ret₂ : o₂.exit=.ret r₂) : r₁=r₂ :=
 (LIBB_ObservationModel.returns env pub proof ck o₁ r₁ h₁ ret₁).trans
  (LIBB_ObservationModel.returns env pub proof ck o₂ r₂ h₂ ret₂).symm

/-- Rev3's reservation-aware resolved graph is Functional at every Env. -/
theorem resolved_functional (pub proof ck : Slice U8) :
 RSL.Spec.Functional (LIBB_EnvValues.graph pub proof ck) := LIBB_EnvValues.functional pub proof ck

#print axioms prefix_no_write
#print axioms piece_no_write
#print axioms pieces_no_write
#print axioms common_no_write
#print axioms observation_no_write
#print axioms writeFree
#print axioms returned_unique
#print axioms resolved_functional
end LIBB_ObservationValues
end
