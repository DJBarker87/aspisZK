import NDO_JFw_Frames
set_option autoImplicit false
namespace AspisR1.JFw_FrameLength
open Aeneas Aeneas.Std

theorem length (tag a b c d : U8) (payload : Slice U8) (small : payload.length ≤ 4000) :
    (JFw_Frames.frame tag a b c d payload small).length = 5+payload.length := by
  simp only [JFw_Frames.frame,Slice.length,List.length_cons]
  omega

#print axioms length
end AspisR1.JFw_FrameLength
