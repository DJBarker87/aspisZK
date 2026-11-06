import NLI_ResourceStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Resource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def fold {A H : Type} (allocator : S2W_D189Wrappers.Allocator (Heap A)) :
 Nat → State A H → Observation A H
 | 0,s => ⟨s.machine.input,[],.fail .panic⟩
 | n+1,s =>
   let head := step allocator s
   match head.reply with
   | .fail e => ⟨head.lastInput,head.trace,.fail e⟩
   | .div => ⟨head.lastInput,head.trace,.div⟩
   | .ok (.inl out) => ⟨head.lastInput,head.trace,ok out⟩
   | .ok (.inr after) =>
     let tail := fold allocator n after
     {tail with trace := head.trace ++ tail.trace}
end AspisR1.NLI_Resource
namespace AspisR1.NLI_FullInterface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish NLI_Resource
abbrev Native (H : Type) := ∀ A : Type,
 S2W_D189Wrappers.Allocator (Heap A) → Heap A → Input H → Observation A H
/-- PROPOSED FULL RESOURCE-CARRIER TARGET, not an admitted packet. The
native function must be the frozen G interpretation, never a function chosen
to satisfy this Prop. It covers complete Result, allocator/rest-heap post,
live Claims owner, input frame, major source occurrences, digest attempt and
allocation/cleanup abort prefix at SAME parsed inputs. Source-site/cleanup
fidelity and nested low/high and try/unwrap occurrence expansion, and all public/challenge caller domains require ledger review before
NLJ may use this as a final child obligation; no Root136 proof is submitted. -/
def RowSpec_136 {H : Type} (native : Native H) : Prop :=
 ∀ (A : Type) (allocator : S2W_D189Wrappers.Allocator (Heap A))
 (heap : Heap A) (base : Input H) (bytes : Slice U8),
 match AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   let input := {base with prefix1 := PrefixAdapter.fromOld pre}
   let observed := native A allocator heap input
   observed.lastInput=input ∧
   observed=NLI_Resource.fold allocator (NLC_Finish.fuel (NLC_Finish.initial input)) (NLI_Resource.initial heap input)
 | _ => True
#print RowSpec_136
end AspisR1.NLI_FullInterface
end
