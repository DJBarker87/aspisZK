import FJl_M31ArrayValue
import FJl_SliceCopy
import FJi_Nonvacuity
import JFr_TX2_Scalars
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_Nonvacuity
open Aeneas Aeneas.Std Result
/-- Strict scalar-byte VALUE transport is inhabited by all 1248 retained
TX2 fixture scalar reads. No concrete arithmetic is replayed. -/
theorem scalar (i : Fin 12) (s : Fin 4) (l : Fin 26) :
    ∃ (a : Array U8 4#usize) (x : U32),
      JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array (JFn_Values.position i))
        (Usize.ofNat s.val (by have:=s.isLt;scalar_tac))
        (Usize.ofNat l.val (by have:=l.isLt;scalar_tac))=ok x ∧
      FIp_DotDecode.field.M31.from_le_bytes a=ok (some x) ∧
      ExactLeafFieldCodec.decodeM31 (MultiproofConeCanonical.bytesOf a.val)=
        some (x.val : ExactLeafFieldCodec.M31Exact) := by
  have run := JFr_TX2_Scalars.source i s l
  obtain ⟨a,hbytes,parse⟩ := FJl_SliceCopy.scalar _ _ _ _ run
  exact ⟨a,_,run,parse,FJl_M31ArrayValue.value a _ parse⟩
#print axioms scalar
end AspisR1.FJl_Nonvacuity
end
