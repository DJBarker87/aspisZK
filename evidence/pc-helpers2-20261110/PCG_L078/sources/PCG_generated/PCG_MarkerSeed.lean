import PCG_PackComposition
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_MarkerSeed
abbrev Key := Array U8 32#usize
def toSlice (key : Key) : Slice U8 := ⟨key.val, by have h := key.property; scalar_tac⟩
def domain : Slice U8 := ⟨[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,109#u8,97#u8,114#u8,107#u8,101#u8,114#u8,45#u8,115#u8,101#u8,101#u8,100#u8,45#u8,118#u8,49#u8], by scalar_tac⟩
def parts (pool encoding : Key) : Slice (Slice U8) :=
 ⟨[domain,toSlice pool,toSlice encoding],by scalar_tac⟩
/-- Only the runtime hash value is trusted; request bytes and ordering are fixed. -/
abbrev Hashv := Slice (Slice U8) → Key

def native (hashv : Hashv) (pool encoding : Key) : Fin 32 → Nat :=
 fun i => PCG_PackComposition.chunks (hashv (parts pool encoding)) 4 i.val

/-- Complete hash-to-pack pipeline, consuming the CLOSED pack result at the
SAME returned digest and deriving each output byte internally. -/
theorem row_296 (hashv : Hashv) (pool encoding : Key) :
 native hashv pool encoding = fun i : Fin 32 => PCG_PackLaw.pack
  (hashv (⟨[domain,toSlice pool,toSlice encoding],by scalar_tac⟩)) i.val := by
 funext i
 exact congrFun (PCG_PackComposition.row_293 (hashv (parts pool encoding))).1 i

theorem exact_request (pool encoding : Key) :
 (parts pool encoding).val = [domain,toSlice pool,toSlice encoding] ∧
 domain.val.length = 20 ∧ (toSlice pool).val.length = 32 ∧
 (toSlice encoding).val.length = 32 := by
 refine ⟨rfl,rfl,?_,?_⟩
 · simpa [toSlice] using pool.property
 · simpa [toSlice] using encoding.property

#print axioms row_296
#print axioms exact_request
end PCG_MarkerSeed
