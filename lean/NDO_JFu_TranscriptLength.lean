import NDO_JFu_TranscriptSeed
set_option autoImplicit false
namespace AspisR1.JFu_TranscriptLength
open Aeneas Aeneas.Std Result WP AspisR1PublicPreparation

theorem converted (bytes : Slice U8) (size : bytes.length=1455) :
    core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes)=ok (.Ok 1455#u32) := by
  have spec : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes)
      ⦃ out => out=.Ok 1455#u32 ⦄ := by
    have len : (Slice.len bytes).val=1455 := by scalar_tac
    step*
    obtain ⟨x,same,value⟩:=out_post1 (by scalar_tac)
    rw [same]
    congr 1
    scalar_tac
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms converted
end AspisR1.JFu_TranscriptLength
