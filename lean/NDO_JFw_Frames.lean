import NDO_JFw_RealExpansion
import JFw_CurrentValidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_Frames
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def window (off n : Nat) : Slice U8 :=
  ⟨(JFx_NativeBytes.proof.val.drop off).take n,by
    have h := JFx_NativeBytes.proof.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem window_length (off n : Nat) (fits : off+n ≤ 57607) :
    (window off n).length = n := by
  have length : JFx_NativeBytes.proof.val.length = 57607 := JFx_NativeBytes.proofBytes_length
  change ((JFx_NativeBytes.proof.val.drop off).take n).length = n
  rw [List.length_take,List.length_drop,length]
  omega

theorem window_bytes (off n : Nat) :
    bytesOf (window off n).val = slice JFz_RowGeometry.wire off n := by
  simp only [window,bytesOf,List.map_take,List.map_drop,slice,JFz_RowGeometry.wire]

theorem flat_length (n : Nat) (b : List U8) (length : b.length = 16*n) :
    (JFw_Blocks.blocks n b).flatten.length = 32*n := by
  have h := congrArg List.length (JFw_Blocks.bytes n b)
  simp only [bytesOf,List.length_map] at h
  rw [PSem_Expand.expand_length n _ (by simp only [bytesOf,List.length_map,length])] at h
  exact h

def expandedPayload (n off : Nat) (small : n ≤ 116) (fits : off+16*n ≤ 57607) : Slice U8 :=
  ⟨(JFw_Blocks.blocks n (window off (16*n)).val).flatten,by
    rw [flat_length n _ (window_length off (16*n) fits)]
    scalar_tac⟩

theorem expanded_length (n off : Nat) (small : n ≤ 116) (fits : off+16*n ≤ 57607) :
    (expandedPayload n off small fits).length = 32*n :=
  flat_length n _ (window_length off (16*n) fits)

theorem expanded_bytes (n off : Nat) (small : n ≤ 116) (fits : off+16*n ≤ 57607) :
    bytesOf (expandedPayload n off small fits).val =
      expand n (slice JFz_RowGeometry.wire off (16*n)) := by
  exact (JFw_Blocks.bytes n _).trans (congrArg (expand n) (window_bytes off (16*n)))

def frame (tag a b c d : U8) (payload : Slice U8) (small : payload.length ≤ 4000) : Slice U8 :=
  ⟨tag::a::b::c::d::payload.val,by
    simp only [List.length_cons]
    change payload.val.length ≤ 4000 at small
    scalar_tac⟩

#print axioms window_length
#print axioms window_bytes
#print axioms flat_length
#print axioms expanded_length
#print axioms expanded_bytes
end AspisR1.JFw_Frames
end
