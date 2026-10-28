import RPv_FJr_KindIndices
import NDO_JGs_KindForward
import NDO_JGs_T4
import NDO_JGs_S40
import NDO_JGs_S41
import NDO_JGs_D4
import NDO_JGs_K3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_K4
open Aeneas Aeneas.Std Result
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def scale : E := ⟨⟨⟨142108701#u32,60139487#u32⟩,⟨989761709#u32,276498178#u32⟩⟩,⟨⟨2107566386#u32,1658435584#u32⟩,⟨930316936#u32,762894097#u32⟩⟩⟩
def value : E := ⟨⟨⟨1362830472#u32,1020991058#u32⟩,⟨911112580#u32,1801526746#u32⟩⟩,⟨⟨1712934562#u32,1784900389#u32⟩,⟨801209518#u32,819971946#u32⟩⟩⟩
def scratch : alloc.vec.Vec Q := ⟨JGs_T4.s21.val,JGs_T4.s21.property⟩
def parts : Array E 7#usize := (JGs_K3.parts).set 6#usize value
theorem multiply : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_S40.value JGs_S41.value=ok scale := by with_unfolding_all rfl
#print axioms multiply
theorem scaled : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale JGs_D4.value=ok value := by with_unfolding_all rfl
#print axioms scaled
/-- This real-byte kind consumes the preceding kind's native scratch and write. -/
theorem source : @FIo_Native.weights.process_kind (FIo_Install.allocation (.Ok ()))
    JGq_PairShape.w 6#usize JGq_PairShape.alpha JGq_PairShape.f 2#usize 64#usize
    JGq_Powers0.a4 JGq_Powers1.a4 JGs_K3.scratch JGs_K3.parts=ok (.Ok (),scratch,parts) := by
  letI := FIo_Install.allocation (.Ok ())
  have row : Array.index_usize JGq_PairShape.w.factors 4#usize=
      ok (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ) JGo_TX2_WeightData.r4_5) := by rfl
  have borrow : alloc.vec.Vec.deref_mut JGs_K3.scratch=
      (JGs_T4.input,fun t : Slice Q=> (⟨t.val,t.property⟩ : alloc.vec.Vec Q)) := by with_unfolding_all rfl
  have write : Array.update JGs_K3.parts 6#usize value=ok parts := by
    obtain ⟨a,ha,eq⟩ := WP.spec_imp_exists (Array.update_spec JGs_K3.parts 6#usize value (by scalar_tac))
    subst a
    exact ha
  exact JGs_KindForward.source JGq_PairShape.w (by rfl) 6#usize 4#usize
    (by simp only [show ¬(6#usize<4#usize) from by decide,ite_false]; apply UScalar.eq_of_val_eq; rw [FJr_KindIndices.sub _ _ (by decide) (by decide)];rfl) JGq_PairShape.alpha JGq_PairShape.f 64#usize JGq_Powers0.a4 JGq_Powers1.a4
    JGs_K3.scratch JGs_T4.input JGs_T4.s21 (fun t=>⟨t.val,t.property⟩) borrow
    _ JGs_S40.row JGs_S41.row JGs_S40.value JGs_S41.value scale JGs_D4.value value
    JGs_D4.d0 JGs_D4.d64 JGs_K3.parts parts JGs_T4.source row (by rfl)
    JGs_S40.source (by rfl) JGs_S41.source multiply (by rfl) JGs_D4.source JGs_D4.finish scaled write
#print axioms source
end AspisR1.JGs_K4
end
