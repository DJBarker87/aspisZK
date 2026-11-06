import NLF_RuntimeInterpretation
set_option autoImplicit false
namespace NLF_InitialBinding
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation

theorem source_counter_zero {F : Type} (h : S2Trust.Heap F) (keys : Nat → List UInt8) (n : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n) (i : Nat) : h.counter i=0 := by
  have eq := (runtime.valid.2.1 i).2.2.1
  simpa [S2Trust.count,runtime.freshGuards,runtime.noExternalBorrows] using eq

theorem all_counter_binding {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (n : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) n) (i : Nat) :
    flag ((install h records money).state.cells i)=h.counter i := by
  rw [source_counter_zero h _ n runtime i]
  rfl

theorem empty_native_guards {F : Type} (h : S2Trust.Heap F) (keys : Nat → List UInt8) (n : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n) :
    h.guards=[] ∧ (∀ i,h.external i=0) := ⟨runtime.freshGuards,runtime.noExternalBorrows⟩

#print axioms source_counter_zero
#print axioms all_counter_binding
#print axioms empty_native_guards
end NLF_InitialBinding
