import NLF_SdkBorrowLaw
set_option autoImplicit false
namespace NLQ_MetadataAdmission
open AspisR1 NLF_SdkModel NLF_RuntimeInterpretation
/-- Approved admission constrains keys, cells, liveness and guard state.
Changing per-occurrence writable metadata does not change any of its fields. -/
def withFlags (records : Nat → Account) (flags : Nat → Bool) (a : Nat) : Account :=
 {records a with writable:=flags a}
theorem admission {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
 (n : Nat) (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) n)
 (flags : Nat → Bool) :
 AdapterRw.RuntimeEntrypointAdmission h (fun a => (withFlags records flags a).key) n := runtime
/-- A shared cell alone cannot justify equal writable flags. This is a fact
about the seven-field admission, not a counterexample to the frozen program
or a claim about a separately proved entrypoint-deserializer invariant. -/
theorem different_flags {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
 (money : Nat → Nat) (n a b : Nat) (different : a≠b)
 (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun i => (records i).key) n)
 (sameCell : (h.accounts a).1=(h.accounts b).1) :
 let changed := withFlags records (fun i => decide (i=b))
 let state := (install h changed money).state
 AdapterRw.RuntimeEntrypointAdmission h (fun i => (changed i).key) n ∧
 (state.accounts a).data=(state.accounts b).data ∧
 (state.accounts a).writable=false ∧ (state.accounts b).writable=true := by
 dsimp only
 refine ⟨admission h records n runtime _,?_,?_,?_⟩
 · exact sameCell
 · simp [install,NLF_Admission.initial,withFlags,different]
 · simp [install,NLF_Admission.initial,withFlags]
#print admission
#print different_flags
#print axioms admission
#print axioms different_flags
end NLQ_MetadataAdmission
