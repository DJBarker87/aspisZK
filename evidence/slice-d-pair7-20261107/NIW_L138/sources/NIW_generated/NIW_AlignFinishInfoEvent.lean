import NIW_AlignFinishComposed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishInfoEvent
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed

def eventOf (info : PairInfo) : Event :=
 .pair info.owner.value info.alpha.value.to_slice info.message.value info.kappa (NIT_ErrorTransport.full info.native.1)

def HasPair {A : Type} (observed : Observed A) : Prop :=
 ∀ info,observed.2.2=some info → eventOf info∈observed.2.1

theorem head_mem {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (next : A → Observed B) : event call∈(observe call event next).2.1 := by
 cases call with
 | fail err => exact List.mem_singleton_self _
 | div => exact List.mem_singleton_self _
 | ok reply =>
  cases reply with
  | Err err => exact List.mem_singleton_self _
  | Ok value => exact List.mem_cons_self

theorem preserve {A B : Type} (call : Result (Reply A)) (event : Result (Reply A) → Event)
 (next : A → Observed B) (tail : ∀ value,call=ok (.Ok value) → HasPair (next value)) :
 HasPair (observe call event next) := by
 cases call with
 | fail err => intro info same;cases same
 | div => intro info same;cases same
 | ok reply =>
  cases reply with
  | Err err => intro info same;cases same
  | Ok value =>
   intro info same
   exact List.mem_cons_of_mem _ (tail value rfl info same)

/-- The stored native pair detail belongs to the actual SAME call event in
finish's chronological stream, including pair fail/div. No independent owner
or independently selected packet result is accepted. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) : HasPair (run r loc v p a) := by
 unfold run
 apply preserve
 intro first firstCall
 apply preserve
 intro claim claimCall
 apply preserve
 intro owner newCall
 intro info same
 have equal : detail r loc owner v p=info := Option.some.inj same
 subst info
 exact head_mem _ _ _

#print axioms head_mem
#print axioms preserve
#print axioms source
end AspisR1.NIW_AlignFinishInfoEvent
