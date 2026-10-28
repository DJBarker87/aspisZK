import RPv_FJr_KindIndices
import NDO_JGs_KindForward
import NDO_JGs_T1
import NDO_JGs_S10
import NDO_JGs_S11
import NDO_JGs_D1
import NDO_JGq_PairPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_K1
open Aeneas Aeneas.Std Result
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def scale : E := ⟨⟨⟨1605662913#u32,1349098180#u32⟩,⟨1533970664#u32,1255888348#u32⟩⟩,⟨⟨1414416824#u32,202426342#u32⟩,⟨1144111966#u32,1065796586#u32⟩⟩⟩
def value : E := ⟨⟨⟨922431642#u32,793310#u32⟩,⟨979152312#u32,935870752#u32⟩⟩,⟨⟨198629376#u32,869677593#u32⟩,⟨2077608530#u32,1073449776#u32⟩⟩⟩
def scratch : alloc.vec.Vec Q := ⟨JGs_T1.s21.val,JGs_T1.s21.property⟩
def parts : Array E 7#usize := (JGq_PairPrefix.initial).set 2#usize value
theorem multiply : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_S10.value JGs_S11.value=ok scale := by with_unfolding_all rfl
#print axioms multiply
theorem scaled : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale JGs_D1.value=ok value := by with_unfolding_all rfl
#print axioms scaled
/-- This real-byte kind consumes the preceding kind's native scratch and write. -/
theorem source : @FIo_Native.weights.process_kind (FIo_Install.allocation (.Ok ()))
    JGq_PairShape.w 2#usize JGq_PairShape.alpha JGq_PairShape.f 2#usize 64#usize
    JGq_Powers0.a4 JGq_Powers1.a4 JGq_PairShape.scratch JGq_PairPrefix.initial=ok (.Ok (),scratch,parts) := by
  letI := FIo_Install.allocation (.Ok ())
  have row : Array.index_usize JGq_PairShape.w.factors 1#usize=
      ok (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ) JGo_TX2_WeightData.r1_5) := by rfl
  have borrow : alloc.vec.Vec.deref_mut JGq_PairShape.scratch=
      (JGs_T1.input,fun t : Slice Q=> (⟨t.val,t.property⟩ : alloc.vec.Vec Q)) := by with_unfolding_all rfl
  have write : Array.update JGq_PairPrefix.initial 2#usize value=ok parts := by
    obtain ⟨a,ha,eq⟩ := WP.spec_imp_exists (Array.update_spec JGq_PairPrefix.initial 2#usize value (by scalar_tac))
    subst a
    exact ha
  exact JGs_KindForward.source JGq_PairShape.w (by rfl) 2#usize 1#usize
    (by simp only [show (2#usize<4#usize) from by decide,ite_true]; apply UScalar.eq_of_val_eq; rw [FJr_KindIndices.sub _ _ (by decide) (by decide)];rfl) JGq_PairShape.alpha JGq_PairShape.f 64#usize JGq_Powers0.a4 JGq_Powers1.a4
    JGq_PairShape.scratch JGs_T1.input JGs_T1.s21 (fun t=>⟨t.val,t.property⟩) borrow
    _ JGs_S10.row JGs_S11.row JGs_S10.value JGs_S11.value scale JGs_D1.value value
    JGs_D1.d0 JGs_D1.d64 JGq_PairPrefix.initial parts JGs_T1.source row (by rfl)
    JGs_S10.source (by rfl) JGs_S11.source multiply (by rfl) JGs_D1.source JGs_D1.finish scaled write
#print axioms source
end AspisR1.JGs_K1
end
