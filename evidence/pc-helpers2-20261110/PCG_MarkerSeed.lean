import PCG_PackLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_MarkerSeed
abbrev Key := Array U8 32#usize
def domain : Slice U8 := Slice.mk [97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,109#u8,97#u8,114#u8,107#u8,101#u8,114#u8,45#u8,115#u8,101#u8,101#u8,100#u8,45#u8,118#u8,49#u8]
def parts (pool encoding : Key) : Slice (Slice U8) :=
 Slice.mk [domain,Slice.mk pool.val,Slice.mk encoding.val]
/-- Only the runtime hash value is trusted; request bytes and ordering are fixed. -/
abbrev Hashv := Slice (Slice U8) → Key

def native (hashv : Hashv) (pool encoding : Key) : Nat → Nat :=
 PCG_PackLaw.pack (hashv (parts pool encoding))

/-- A complete caller pipeline with the child pack model at the SAME digest.
Closure additionally needs the full source-loop induction for POOL:293. -/
theorem row_296 (hashv : Hashv) (pool encoding : Key) :
 native hashv pool encoding = PCG_PackLaw.pack
  (hashv (Slice.mk [domain,Slice.mk pool.val,Slice.mk encoding.val])) := rfl

theorem exact_request (pool encoding : Key) :
 (parts pool encoding).val = [domain,Slice.mk pool.val,Slice.mk encoding.val] ∧
 domain.val.length = 20 ∧ (Slice.mk pool.val).val.length = 32 ∧
 (Slice.mk encoding.val).val.length = 32 := by
 refine ⟨rfl,rfl,?_,?_⟩
 · simpa using pool.property
 · simpa using encoding.property

#print axioms row_296
#print axioms exact_request
end PCG_MarkerSeed
