import NMB_MetadataBorrow
set_option autoImplicit false
namespace NMB_MetadataAdmission
open AspisR1 NLF_SdkModel NLF_RuntimeInterpretation
/-- Per-occurrence records enter the approved installation unchanged except
for the SAME heap's data and lamport handles. Cell aliases impose no flag law. -/
theorem installation {F : Type} (h : S2Trust.Heap F)
 (before after : Nat → Account) (money : Nat → Nat) :
 NMB_Metadata.install (install h before money).state after =
 (install h after money).state := rfl
/-- Runtime admission follows the input keys, rather than cell-indexed metadata.
The key equation is an own-input association, never an extra ABI trust item. -/
theorem admission {F : Type} (h : S2Trust.Heap F) (keys : Nat → List UInt8)
 (r : Nat → Account) (n : Nat)
 (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n)
 (same : ∀ a, (r a).key = keys a) :
 AdapterRw.RuntimeEntrypointAdmission h (fun a => (r a).key) n := by
 have eq : (fun a => (r a).key) = keys := funext same
 rw [eq]
 exact runtime
#print admission
#print axioms installation
#print axioms admission
end NMB_MetadataAdmission
