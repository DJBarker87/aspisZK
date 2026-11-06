import NKA_InitializedPrefix
set_option autoImplicit false
namespace AspisR1.NKA_InitHistory
open Aeneas Aeneas.Std
/-- Each entry records completion of a typed [QM31;29] ptr::write at that
source row. This is a fresh-allocation history, not a value-equality test. -/
abbrev History := List (Fin 3)
structure Storage where
 memory : NKA_InitializedPrefix.Memory
 writes : History

def Ready (storage : Storage) : Prop := ∀ p : Fin 3,p∈storage.writes

def completed (memory : NKA_InitializedPrefix.Memory) : Storage := ⟨memory,[2,1,0]⟩

theorem ready (memory : NKA_InitializedPrefix.Memory) : Ready (completed memory) := by
 intro p
 have alternatives : p.val=0 ∨ p.val=1 ∨ p.val=2 := by omega
 rcases alternatives with h | h | h
 · have same : p=0 := Fin.ext h
   simp [completed,same]
 · have same : p=1 := Fin.ext h
   simp [completed,same]
 · have same : p=2 := Fin.ext h
   simp [completed,same]

#print axioms ready
end AspisR1.NKA_InitHistory
