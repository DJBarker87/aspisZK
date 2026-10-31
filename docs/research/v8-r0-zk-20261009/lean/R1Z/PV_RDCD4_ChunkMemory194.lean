import R1Z.PV_RDCD4_MemorySplit194
import R1Z.PV_RDCD4_Chunks194
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_ChunkMemory194
open PV_RDCD4_Memory194
set_option autoImplicit false

/-- split_at_checked followed by the source and_then closure's v store. -/
def source {E : Type} (v rem : Span E) : Option (Span E) × (Span E × Span E) :=
  match PV_RDCD4_MemorySplit194.checked v 2 with
  | none => (none,(v,rem))
  | some (chunk,rest) => (some chunk,(rest,rem))

def project {E : Type} (r : Option (Span E) × (Span E × Span E)) :
    Option (List E) × PV_RDCD4_Chunks194.State E :=
  (r.1.map values,⟨values r.2.1,values r.2.2⟩)

theorem binding {E : Type} (v rem : Span E) (hv : valid v.pointer v.len) :
    project (source v rem)=
      PV_RDCD4_Chunks194.next ⟨values v,values rem⟩ := by
  have hl : (values v).length=v.len := length v.pointer v.len hv
  by_cases hm : 2 ≤ v.len
  · have h : 2 ≤ (values v).length := by rw [hl]; exact hm
    simp only [source,PV_RDCD4_MemorySplit194.checked,if_pos hm,project,
      Option.map_some,PV_RDCD4_Chunks194.next,if_pos h]
    rw [PV_RDCD4_MemorySplit194.left_values v 2 hm,
      PV_RDCD4_MemorySplit194.right_values]
  · have h : ¬2 ≤ (values v).length := by rw [hl]; exact hm
    simp only [source,PV_RDCD4_MemorySplit194.checked,if_neg hm,project,
      Option.map_none,PV_RDCD4_Chunks194.next,if_neg h]

#print axioms binding
end R1Z.PV_RDCD4_ChunkMemory194
