import NJR_SourceFinishReads
import NJR_DecodedWords
set_option autoImplicit false
noncomputable section
namespace NJR_WindowsFromFinish
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Stage2Finish

theorem polynomial (bytes : Slice U8) (length : bytes.val.length=224)
 (reads : ∀ i : Usize,i.val<7→∃ c,FIn_Primitives.field bytes i=ok c) :
 NIG_FinishInput.Windows bytes 7 := by
 refine ⟨length,?_⟩
 intro i hi j hj
 let index : Usize:=Usize.ofNat i (by
  have cap : 7 ≤ UScalar.cMax UScalarTy.Usize := by scalar_tac
  omega)
 have indexVal : index.val=i := by rfl
 obtain ⟨c,read⟩:=reads index (by rw [indexVal];exact hi)
 have decoded:=FIn_Primitives.field_value bytes index c read
 have bound:=NJR_DecodedWords.window bytes (32*index.val) (by rw [length,indexVal];omega)
  _ decoded ⟨j,hj⟩
 simpa only [indexVal] using bound

theorem dot (bytes : Slice U8) (length : bytes.val.length=2048)
 (reads : ∀ i : Fin 64,∃ index value,index.val=i.val ∧
  AspisR1CurrentWide.Proof.finishField bytes index=ok value) :
 NIG_FinishInput.Windows bytes 64 := by
 refine ⟨length,?_⟩
 intro i hi j hj
 obtain ⟨index,value,indexVal,read⟩:=reads ⟨i,hi⟩
 have decoded:=SAG_FieldRead.from_finish bytes index value read
 have bound:=NJR_DecodedWords.window bytes (32*index.val) (by rw [length,indexVal];change 32*i+32≤2048;omega)
  _ decoded ⟨j,hj⟩
 simpa only [indexVal] using bound

/-- Source acceptance yields the raw bounds, including every accessed field.
This is a source-history inversion lemma, NOT a positive native root and NOT
permission to add a successful finish premise to one. The actual caller must
derive this SAME call as part of its own accepted history before using it. -/
theorem source (r : NP6_StdModel.Reservation) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) (s2 : p.variant=.S2)
 (width : a.weights.val.length=64)
 (r0size : v.round0.val.length=224) (r1size : v.round1.val.length=224)
 (finalSize : v.final_message.val.length=2048)
 (run : Port4D_FinishInstall.finish (IDa_Deployed.finish r) v p a none=ok (.Ok ())) :
 NIG_FinishInput.Windows v.round0 7 ∧ NIG_FinishInput.Windows v.round1 7 ∧
 NIG_FinishInput.Windows v.final_message 64 := by
 obtain ⟨r0,r1,final⟩:=NJR_SourceFinishReads.source r v p a s2 width run
 exact ⟨polynomial v.round0 r0size r0,polynomial v.round1 r1size r1,dot v.final_message finalSize final⟩

#print axioms polynomial
#print axioms dot
#print axioms source
end NJR_WindowsFromFinish
