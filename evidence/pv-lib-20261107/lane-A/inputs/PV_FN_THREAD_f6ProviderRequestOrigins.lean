import PV_FN_THREAD_f6ProviderRequestSyntax
set_option autoImplicit false
namespace PV_FN_THREAD_f6ProviderRequestOrigins
open PV_STX2_Syntax PV_STX2_SliceSyntax
open PV_FN_THREAD_f6ProviderRequestSyntax

/-- Generic source-origin elimination. Once a reached instruction is known to
belong to the emitted body, its callee is obtained from the proved syntax
projection. This theorem does not assume or assert a runtime origin invariant. -/
theorem call_mem (p : PV_STX2_SliceSyntax.Program) (site : Site) (fn : Data)
    (args : List Operand) (dest : Place) (cleanup : List Instruction)
    (origin : .leaf (.call site fn args dest cleanup) ∈ p.body) :
    (site.statement,PV_THR2_OffPath.functionId fn) ∈ calls p := by
  apply List.mem_filterMap.mpr
  exact ⟨_,origin,rfl⟩

/-- No constructor body can issue320 from one of its emitted call instructions.
The named local table lemmas cover all seven numeric ids. The BoxNew exception
is its own exact token and has no numeric function id. -/
theorem constructor_not320 (p : PV_STX2_SliceSyntax.Program)
    (body : p = PV_THR2_F124.live ∨ p = PV_THR2_F216.live ∨
      p = PV_THR2_F218.live ∨ p = PV_THR2_F315.live)
    (site : Site) (fn : Data) (args : List Operand) (dest : Place)
    (cleanup : List Instruction)
    (origin : .leaf (.call site fn args dest cleanup) ∈ p.body) :
    PV_THR2_OffPath.functionId fn ≠ some 320 := by
  have member := call_mem p site fn args dest cleanup origin
  rcases body with h | h | h | h <;> subst p
  · rw [constructor_calls.1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with h | h | h | h | h | h <;> intro equal <;>
      rw [equal] at h <;> cases h.2
  · rw [constructor_calls.2.1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with h | h <;> intro equal <;> rw [equal] at h <;> cases h.2
  · rw [constructor_calls.2.2.1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    intro equal
    rw [equal] at member
    cases member.2
  · rw [constructor_calls.2.2.2] at member
    exact False.elim (List.not_mem_nil member)

/-- The dereference cone has one structured call and one opaque call. The
native receiver/value/world are separately supplied by provider Post and Pre. -/
theorem deref_ids (p : PV_STX2_SliceSyntax.Program)
    (body : p = PV_THR2_F126.live ∨ p = PV_THR2_F222.live)
    (site : Site) (fn : Data) (args : List Operand) (dest : Place)
    (cleanup : List Instruction)
    (origin : .leaf (.call site fn args dest cleanup) ∈ p.body) :
    PV_THR2_OffPath.functionId fn = some 222 ∨
      PV_THR2_OffPath.functionId fn = some 320 := by
  have member := call_mem p site fn args dest cleanup origin
  rcases body with h | h <;> subst p
  · rw [deref_calls.1] at member
    exact Or.inl (congrArg Prod.snd (List.mem_singleton.mp member))
  · rw [deref_calls.2] at member
    exact Or.inr (congrArg Prod.snd (List.mem_singleton.mp member))

#print axioms call_mem
#print axioms constructor_not320
#print axioms deref_ids
end PV_FN_THREAD_f6ProviderRequestOrigins
