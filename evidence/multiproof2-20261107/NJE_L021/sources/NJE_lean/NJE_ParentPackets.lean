import NJA_ParentCut
import NGC_DigestBridge

set_option autoImplicit false
noncomputable section
namespace NJE_ParentPackets
open Aeneas Aeneas.Std Result NJA_Multiproof
open AspisR1.MultiproofConePhysicalDigest
abbrev Digest := Array U8 32#usize

-- Explicit transport of the CLOSED deployed digest dictionary. No new oracle,
-- hash-value or totality assumption. NGC forwarding is instantiated at SAME parts.
def backend (hashv : Slice (Slice U8) → Digest) : aspis_core.digest.Digest32 Unit where
 coremarkerCopyInst := { cloneInst := { clone := fun x => ok x } }
 digest := fun _ parts => (AspisR1.NGC_DigestBridge.backend hashv).digest () parts

def cell (values : Array Digest 16#usize) (i : Nat) : Digest := values.val[i]!

theorem TX1_123 (hashv : Slice (Slice U8) → Digest)
    (values : Array Digest 16#usize) (i : Usize) (bound : i.val+1<16) :
    multiproof.occupied_binary_parent (backend hashv) () values i =
      ok (hashv (parts (cell values i.val) (cell values (i.val+1)))) := by
 rw [NJA_ParentAddress.occupied (backend hashv) () values i bound]
 simp only [backend,AspisR1.NGC_DigestBridge.forwarding]
 simp only [cell, getElem!_pos values.val i.val (by have h : values.val.length=16 := values.property; omega),
   getElem!_pos values.val (i.val+1) (by have h : values.val.length=16 := values.property; omega)]

theorem TX2_089 (hashv : Slice (Slice U8) → Digest)
    (values : Array Digest 16#usize) (i : Usize) (bound : i.val+1<16) :
    multiproof.occupied_binary_parent (backend hashv) () values i =
      ok (hashv (parts (cell values i.val) (cell values (i.val+1)))) :=
 TX1_123 hashv values i bound

theorem TX1_125 (hashv : Slice (Slice U8) → Digest)
    (values : Array Digest 16#usize) (i : Usize) (bound : i.val<16)
    (sibling : Digest) (left : Bool) :
    multiproof.sibling_binary_parent (backend hashv) () values i (Array.to_slice sibling) left =
      ok (hashv (if left then parts (cell values i.val) sibling else parts sibling (cell values i.val))) := by
 cases left
 · rw [NJA_ParentAddress.sibling_right (backend hashv) () values i bound]
   simp only [backend,AspisR1.NGC_DigestBridge.forwarding,Bool.false_eq_true,if_false]
   congr 2
   simp only [parts,cell,Array.to_slice,
     getElem!_pos values.val i.val (by have h : values.val.length=16 := values.property; omega)]
 · rw [NJA_ParentAddress.sibling_left (backend hashv) () values i bound]
   simp only [backend,AspisR1.NGC_DigestBridge.forwarding,if_true]
   congr 2
   simp only [parts,cell,Array.to_slice,
     getElem!_pos values.val i.val (by have h : values.val.length=16 := values.property; omega)]

theorem TX2_091 (hashv : Slice (Slice U8) → Digest)
    (values : Array Digest 16#usize) (i : Usize) (bound : i.val<16)
    (sibling : Digest) (left : Bool) :
    multiproof.sibling_binary_parent (backend hashv) () values i (Array.to_slice sibling) left =
      ok (hashv (if left then parts (cell values i.val) sibling else parts sibling (cell values i.val))) :=
 TX1_125 hashv values i bound sibling left

#print TX1_123
#print axioms TX1_123
#print TX2_089
#print axioms TX2_089
#print TX1_125
#print axioms TX1_125
#print TX2_091
#print axioms TX2_091
end NJE_ParentPackets
end
