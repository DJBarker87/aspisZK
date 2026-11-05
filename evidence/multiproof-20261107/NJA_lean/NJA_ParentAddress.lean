import NJA_Reads
import MultiproofConePhysicalDigest

set_option autoImplicit false
noncomputable section
namespace NJA_ParentAddress
open Aeneas Aeneas.Std Result NJA_Multiproof
open AspisR1.MultiproofConePhysicalDigest

abbrev Digest := Array U8 32#usize

theorem occupied {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (values : Array Digest 16#usize) (i : Usize) (hi : i.val + 1 < 16) :
    multiproof.occupied_binary_parent D hash values i =
      D.digest hash (parts
        (values.val[i.val]'(by have len : values.val.length = 16 := values.property; omega))
        (values.val[i.val+1]'(by have len : values.val.length = 16 := values.property; omega))) := by
  unfold multiproof.occupied_binary_parent multiproof.BINARY_NODE_TAG
  simp only [lift, bind_tc_ok]
  have ib : i.val < (16#usize).val := by scalar_tac
  rw [NJA_Reads.index_ok values i ib]
  simp only [bind_tc_ok]
  have next : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    change i.val + 1 < UScalar.size .Usize
    exact lt_trans (show i.val + 1 < (16#usize).val by scalar_tac) (16#usize).hSize
  rw [NJA_Reads.index_ok values (Usize.wrapping_add i 1#usize) (by scalar_tac)]
  simp [Array.to_slice, Array.make, parts, next, lift]

theorem sibling_left {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (values : Array Digest 16#usize) (i : Usize) (hi : i.val < 16)
    (sibling : Slice U8) :
    multiproof.sibling_binary_parent D hash values i sibling true =
      D.digest hash
        ⟨[⟨[18#u8],by simp; scalar_tac⟩,
          ⟨(values.val[i.val]'(by have len : values.val.length = 16 := values.property; omega)).val,
            by have h := (values.val[i.val]'(by have len : values.val.length = 16 := values.property; omega)).property; scalar_tac⟩,
          sibling],by simp; scalar_tac⟩ := by
  unfold multiproof.sibling_binary_parent multiproof.BINARY_NODE_TAG
  simp only [Bool.true_eq, if_true]
  rw [NJA_Reads.index_ok values i (by scalar_tac)]
  simp [Array.to_slice, Array.make, lift]

theorem sibling_right {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (values : Array Digest 16#usize) (i : Usize) (hi : i.val < 16)
    (sibling : Slice U8) :
    multiproof.sibling_binary_parent D hash values i sibling false =
      D.digest hash
        ⟨[⟨[18#u8],by simp; scalar_tac⟩, sibling,
          ⟨(values.val[i.val]'(by have len : values.val.length = 16 := values.property; omega)).val,
            by have h := (values.val[i.val]'(by have len : values.val.length = 16 := values.property; omega)).property; scalar_tac⟩],
          by simp; scalar_tac⟩ := by
  unfold multiproof.sibling_binary_parent multiproof.BINARY_NODE_TAG
  simp only [Bool.false_eq_true, if_false]
  rw [NJA_Reads.index_ok values i (by scalar_tac)]
  simp [Array.to_slice, Array.make, lift]

#print axioms sibling_right
#print axioms occupied
#print axioms sibling_left
end NJA_ParentAddress
end
