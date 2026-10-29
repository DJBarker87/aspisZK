import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_ConcreteDrop
open PV_W_Threading PV_OWN_Heap PV_OWN_Operations
/-- Concrete POD Vec layouts consumed by the four rows. Source/MIR binding is
separately recorded; these equations alone do not establish native glue. -/
def header (capacity width alignment owner : Nat) : Cell :=
 ⟨capacity*width,alignment,capacity,fun _ => none,owner,true⟩

theorem positive_request {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (t : Token) (cap width alignment owner : Nat) (w : State S X)
 (positive:cap*width≠0) :
 (dropVecPod dealloc t (header cap width alignment owner) w).calls=
 [(w,.deallocate t.address (cap*width) alignment)] := by
 simp [dropVecPod,header,positive,free,emit]

theorem zero_request {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (t : Token) (width alignment owner : Nat) (w : State S X) :
 (dropVecPod dealloc t (header 0 width alignment owner) w).calls=[] := by
 simp [dropVecPod,header,dropPod,lift]

theorem row_layouts : (254*8=2032) ∧ (272*2=544) ∧ (69*1=69) ∧ (1024*24=24576) := by decide

/-- Stack array POD glue never calls the allocator in this explicit model. -/
theorem array_no_heap {S X E : Type} (w : State S X) :
 (dropPod (E:=E) w).calls=[] := rfl
#print axioms positive_request
#print axioms zero_request
#print axioms row_layouts
#print axioms array_no_heap
end R1Z.PV_OWN_ConcreteDrop
