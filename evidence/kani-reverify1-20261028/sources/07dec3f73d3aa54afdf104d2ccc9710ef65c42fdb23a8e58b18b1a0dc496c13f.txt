import KMY_RootComposition
import KMY_ViewComposition
set_option autoImplicit false
namespace KMY_Final
open KMY_WindowComposition KMY_SerializerComposition KMY_VectorComposition

theorem expand (source before : Nat → Nat) (pos j : Nat) :
    window (fun _ => 0) (window source before pos 16) (pos+16) 16 j =
      if pos ≤ j ∧ j < pos+16 then source (j-pos)
      else if pos+16 ≤ j ∧ j < pos+32 then 0 else before j :=
  LPn_step_frame source before pos j

theorem view_input {α β : Type} (decode : (Fin 32 → α) → β)
    (source before : Nat → α) (pos : Nat) :
    decode (fun j => window source before pos 32 (pos+j.val)) =
      decode (fun j => source j.val) :=
  KMY_ViewComposition.decode_window32 decode source before pos

theorem six_wide (raw : Nat → Nat → Nat → Nat) (before : Nat → Nat)
    (j : Nat) (bound : j<192) :
    windows (wideByte raw) before 0 32 6 j = raw (j/32) ((j%32)/4) (j%4) :=
  wide_six raw before j bound

theorem semantic_z (semantic : Nat → Nat → Nat) (z : Nat → Nat → Nat → Nat)
    (before : Nat → Nat) (j : Nat) (bound : j<224) :
    windows (fun b => if b<160 then semantic (b/16) (b%16)
      else z ((b-160)/32) (((b-160)%32)/16) (b%16)) before 0 16 14 j =
      if j<160 then semantic (j/16) (j%16)
      else z ((j-160)/32) (((j-160)%32)/16) (j%16) :=
  KMY_CheckpointComposition.semantic_z_cut semantic z before j bound

theorem semantic_z_length : 14*16=224 := rfl

#print axioms expand
#print axioms view_input
#print axioms six_wide
#print axioms semantic_z
#print axioms semantic_z_length
#print axioms KMY_VectorComposition.six_lengths
#print axioms KMY_VectorComposition.to_vec_value
#print axioms KMY_VectorComposition.growth_retains
#print axioms KMY_RootComposition.roots_queries_bytes
#print axioms KMY_SerializerComposition.joined_digest
#print axioms KMX_CopyMeaning.loop_spec
#print axioms KMX_CopyMeaning.append_spec
#print axioms KMX_CopyMeaning.realloc_prefix
end KMY_Final
