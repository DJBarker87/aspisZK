import LIBC_CohortHash
import MultiproofConePhysicalDigest
set_option autoImplicit false
noncomputable section
namespace LIBC_HashShapes
open Aeneas Aeneas.Std AspisR1
/-- The source's binary-node syscall partitions, for every pair of digests. -/
theorem node (left right : Array U8 32#usize) :
 LIBC_HashPartitions.Shape (NNC_ResumeEvents.parts (MultiproofConePhysicalDigest.parts left right)) := by
 refine ⟨NNC_ByteCarriers.host [18#u8],NNC_ByteCarriers.host left.val,
  NNC_ByteCarriers.host right.val,rfl,?_,Or.inl ⟨?_,?_⟩⟩
 · simpa only [NNC_ByteCarriers.host,List.length_map] using right.property
 · rfl
 · simpa only [NNC_ByteCarriers.host,List.length_map] using left.property
theorem leaf_parts (tag : U8) (value salt : Slice U8) (vs : value.val.length=128 ∨ value.val.length=480)
 (ss : salt.val.length=32) :
 LIBC_HashPartitions.Shape (NNC_ResumeEvents.parts (Port4B_LeafCode.parts tag value salt)) := by
 refine ⟨NNC_ByteCarriers.host [16#u8,tag],NNC_ByteCarriers.host value.val,
  NNC_ByteCarriers.host salt.val,rfl,?_,Or.inr ⟨?_,?_⟩⟩
 · simpa only [NNC_ByteCarriers.host,List.length_map] using ss
 · rfl
 · simpa only [NNC_ByteCarriers.host,List.length_map] using vs
theorem leaf (kind : Usize) (q : Slice U8) (size : q.val.length=832) :
 LIBC_HashPartitions.Shape (NNC_ResumeEvents.parts (Port4B_LeafCode.input kind q)) := by
 have range (s e : Usize) (order : s.val≤e.val) (fit : e.val≤832) :=
  MultiproofConeSlices.sub_length q s e order (by omega)
 unfold Port4B_LeafCode.input
 split
 · apply leaf_parts
   · right;simpa using range 0#usize 480#usize (by decide) (by decide)
   · simpa using range 608#usize 640#usize (by decide) (by decide)
 · split
   · apply leaf_parts
     · left;simpa using range 480#usize 608#usize (by decide) (by decide)
     · simpa using range 640#usize 672#usize (by decide) (by decide)
   · apply leaf_parts
     · left;simpa using range 672#usize 800#usize (by decide) (by decide)
     · simpa using range 800#usize 832#usize (by decide) (by decide)
/-- No flatten-extensionality assumption on Env.sha256 is needed. -/
theorem node_backend (env : RSL.Env) (left right : Array U8 32#usize) :
 (NJS_RuntimeDigest.backend (LIBC_CohortHash.H env)).digest () (MultiproofConePhysicalDigest.parts left right) =
 LIB_Env.hashv env (MultiproofConePhysicalDigest.parts left right) :=
 LIBC_CohortHash.backend env _ (node left right)
theorem leaf_backend (env : RSL.Env) (kind : Usize) (q : Slice U8) (size : q.val.length=832) :
 (NJS_RuntimeDigest.backend (LIBC_CohortHash.H env)).digest () (Port4B_LeafCode.input kind q) =
 LIB_Env.hashv env (Port4B_LeafCode.input kind q) :=
 LIBC_CohortHash.backend env _ (leaf kind q size)
#print axioms node
#print axioms leaf_parts
#print axioms leaf
#print axioms node_backend
#print axioms leaf_backend
end LIBC_HashShapes
