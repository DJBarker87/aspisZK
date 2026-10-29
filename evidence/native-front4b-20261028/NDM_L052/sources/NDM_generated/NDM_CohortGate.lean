import NDM_CohortCommon
import NDM_GateTotal
set_option autoImplicit false
namespace NDM_CohortGate
open Aeneas Aeneas.Std Result
abbrev RawOptionEq (i : core.cmp.PartialEq U64 U64) := AspisR1AdapterReconstruct.core.option.Option.Insts.CoreCmpPartialEqOption i
abbrev RawFieldEq := AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31

theorem option_reference (live next : U64)
 (someTag : (read_discriminant (some next) : Isize)≠0#isize) :
 (do let o ← lift (U64.checked_add live 1#u64)
     core.cmp.PartialEq.ne.trait_default (RawOptionEq core.cmp.PartialEqU64) o (some next)) =
 (do let accepted ← NDM_GateRef.next_gate_ref live next
     ok (!accepted)) := by
 unfold NDM_GateRef.next_gate_ref
 cases call : U64.checked_add live 1#u64 <;>
  simp [lift,core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
   RawOptionEq,AspisR1AdapterReconstruct.core.option.Option.Insts.CoreCmpPartialEqOption,
   AspisR1AdapterReconstruct.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
   core.cmp.PartialEqU64,liftFun2,core.cmp.impls.PartialEqU64.eq] <;> scalar_tac

theorem field_reference (x y : U32) :
 core.cmp.PartialEq.ne.trait_default RawFieldEq x y=ok (decide (x≠y)) := by
 by_cases h : x=y
 · subst y
   simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    RawFieldEq,AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
 · simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    RawFieldEq,AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,h]

theorem option_natural (live next : U64)
 (someTag : (read_discriminant (some next) : Isize)≠0#isize) :
 (do let o ← lift (U64.checked_add live 1#u64)
     core.cmp.PartialEq.ne.trait_default (RawOptionEq core.cmp.PartialEqU64) o (some next)) =
 ok (!(decide (live.val+1=next.val))) := by
 rw [option_reference live next someTag,NDM_GateTotal.reference]
 rfl

#print axioms option_reference
#print axioms field_reference
#print axioms option_natural
end NDM_CohortGate
