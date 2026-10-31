import R1Z.PV_RDCD4_MemorySplit194
import R1Z.PV_RDCD4_Chunks194
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_ChunkCtor194
open PV_RDCD4_Memory194
set_option autoImplicit false

/-- Complete fixed-size-two constructor: compute remainder, split, retain
both spans. The source field chunk_size is initialized to2 and never changed. -/
def source {E : Type} (s : Span E) : Span E × Span E :=
  let rem := s.len % 2
  PV_RDCD4_MemorySplit194.split s (s.len-rem)

def project {E : Type} (s : Span E × Span E) : PV_RDCD4_Chunks194.State E :=
  ⟨values s.1,values s.2⟩

theorem binding {E : Type} (s : Span E) (hv : valid s.pointer s.len) :
    project (source s)=PV_RDCD4_Chunks194.new (values s) := by
  have hl : (values s).length=s.len := length s.pointer s.len hv
  unfold source project
  rw [PV_RDCD4_MemorySplit194.left_values s _ (Nat.sub_le _ _),
    PV_RDCD4_MemorySplit194.right_values]
  simp only [PV_RDCD4_Chunks194.new,hl]

#print axioms binding
end R1Z.PV_RDCD4_ChunkCtor194
