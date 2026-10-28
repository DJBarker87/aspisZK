import RPv_FJr_KindIndices
import NDO_JGs_KindForward
import NDO_JGs_T3
import NDO_JGs_S30
import NDO_JGs_S31
import NDO_JGs_D3
import NDO_JGs_K1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_K3
open Aeneas Aeneas.Std Result
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def scale : E := ⟨⟨⟨99084771#u32,262402828#u32⟩,⟨166321292#u32,858289378#u32⟩⟩,⟨⟨841097164#u32,1325936670#u32⟩,⟨1691344215#u32,1372448173#u32⟩⟩⟩
def value : E := ⟨⟨⟨1889485739#u32,1385206905#u32⟩,⟨2023120663#u32,199654803#u32⟩⟩,⟨⟨946146101#u32,1428322231#u32⟩,⟨182882103#u32,740202615#u32⟩⟩⟩
def scratch : alloc.vec.Vec Q := ⟨JGs_T3.s21.val,JGs_T3.s21.property⟩
def parts : Array E 7#usize := (JGs_K1.parts).set 5#usize value
theorem multiply : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_S30.value JGs_S31.value=ok scale := by with_unfolding_all rfl
#print axioms multiply
theorem scaled : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale JGs_D3.value=ok value := by with_unfolding_all rfl
#print axioms scaled
/-- This real-byte kind consumes the preceding kind's native scratch and write. -/
theorem source : @FIo_Native.weights.process_kind (FIo_Install.allocation (.Ok ()))
    JGq_PairShape.w 5#usize JGq_PairShape.alpha JGq_PairShape.f 2#usize 64#usize
    JGq_Powers0.a4 JGq_Powers1.a4 JGs_K1.scratch JGs_K1.parts=ok (.Ok (),scratch,parts) := by
  letI := FIo_Install.allocation (.Ok ())
  have row : Array.index_usize JGq_PairShape.w.factors 3#usize=
      ok (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ) JGo_TX2_WeightData.r3_5) := by rfl
  have borrow : alloc.vec.Vec.deref_mut JGs_K1.scratch=
      (JGs_T3.input,fun t : Slice Q=> (⟨t.val,t.property⟩ : alloc.vec.Vec Q)) := by with_unfolding_all rfl
  have write : Array.update JGs_K1.parts 5#usize value=ok parts := by
    obtain ⟨a,ha,eq⟩ := WP.spec_imp_exists (Array.update_spec JGs_K1.parts 5#usize value (by scalar_tac))
    subst a
    exact ha
  exact JGs_KindForward.source JGq_PairShape.w (by rfl) 5#usize 3#usize
    (by simp only [show ¬(5#usize<4#usize) from by decide,ite_false]; apply UScalar.eq_of_val_eq; rw [FJr_KindIndices.sub _ _ (by decide) (by decide)];rfl) JGq_PairShape.alpha JGq_PairShape.f 64#usize JGq_Powers0.a4 JGq_Powers1.a4
    JGs_K1.scratch JGs_T3.input JGs_T3.s21 (fun t=>⟨t.val,t.property⟩) borrow
    _ JGs_S30.row JGs_S31.row JGs_S30.value JGs_S31.value scale JGs_D3.value value
    JGs_D3.d0 JGs_D3.d64 JGs_K1.parts parts JGs_T3.source row (by rfl)
    JGs_S30.source (by rfl) JGs_S31.source multiply (by rfl) JGs_D3.source JGs_D3.finish scaled write
#print axioms source
end AspisR1.JGs_K3
end
