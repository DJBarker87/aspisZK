import RPv_FJe_ThreeCell
import RPv_FJb_M31Step
import RPv_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ThreeColumnStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FJb_M31Step (Constants Bounded)
open FJb_MatrixGroupStep (State)
open FJb_TailCell (cell)
abbrev Weights := Array NQ 3#usize
def model (w : Weights) (c0 c1 c2 : Constants) (j : Fin (16#usize).val) : K :=
  decoded w ⟨0,by decide⟩*((cell c0 j).val : K)+decoded w ⟨1,by decide⟩*((cell c1 j).val : K)+
    decoded w ⟨2,by decide⟩*((cell c2 j).val : K)
def step (w : Weights) (c0 c1 c2 : Constants) (s : State) (i : Usize) : Result State := do
  let w0 ← Array.index_usize w 0#usize
  let w1 ← Array.index_usize w 1#usize
  let w2 ← Array.index_usize w 2#usize
  let k0 ← Array.index_usize c0 i
  let k1 ← Array.index_usize c1 i
  let k2 ← Array.index_usize c2 i
  let q ← FJe_ThreeCell.source w0 w1 w2 k0 k1 k2
  Array.update s i q

theorem value (w : Weights) (c0 c1 c2 : Constants) (s out : State) (i : Usize)
    (hi : i.val<(16#usize).val) (hw : canonical w)
    (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) (hs : canonical s)
    (run : step w c0 c1 c2 s i=ok out) :
    canonical out ∧ decoded out=Function.update (decoded s) ⟨i.val,hi⟩
      (model w c0 c1 c2 ⟨i.val,hi⟩) := by
  unfold step at run
  obtain ⟨w0,r0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨w1,r1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨w2,r2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨k0,rk0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨k1,rk1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨k2,rk2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q,rq,run⟩ := FIv_Map.bind_success _ _ _ run
  have ec0 : k0=cell c0 ⟨i.val,hi⟩ := Result.ok.inj
    (rk0.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok c0 i hi))
  have ec1 : k1=cell c1 ⟨i.val,hi⟩ := Result.ok.inj
    (rk1.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok c1 i hi))
  have ec2 : k2=cell c2 ⟨i.val,hi⟩ := Result.ok.inj
    (rk2.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok c2 i hi))
  have ew0 := FIw_ArrayReadValue.read w 0#usize (by decide) w0 r0
  have ew1 := FIw_ArrayReadValue.read w 1#usize (by decide) w1 r1
  have ew2 := FIw_ArrayReadValue.read w 2#usize (by decide) w2 r2
  obtain ⟨v,rv,cv,vv⟩ := FJe_ThreeCell.source_success w0 w1 w2 k0 k1 k2
    (FIv_NativeArray.canonical w 0#usize w0 hw r0)
    (FIv_NativeArray.canonical w 1#usize w1 hw r1)
    (FIv_NativeArray.canonical w 2#usize w2 hw r2)
    (by rw [ec0];exact h0 _) (by rw [ec1];exact h1 _) (by rw [ec2];exact h2 _)
  have eqv : q=v := Result.ok.inj (rq.symm.trans rv)
  subst q
  have vu := FIw_ArrayValue.update s out i v hi hs cv run
  refine ⟨vu.1,vu.2.trans ?_⟩
  apply congrArg (Function.update (decoded s) (⟨i.val,hi⟩ : Fin (16#usize).val))
  simpa only [model,ew0,ew1,ew2,ec0,ec1,ec2,
    show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
    show (2#usize).val=2 from rfl] using vv

theorem unfold_loop (w : Weights) (c0 c1 c2 : Constants) (s : State) (i : Usize) :
    state_only_poseidon.interpolate_three_constant_columns_loop w c0 c1 c2 s i=
      (if i<poseidon2.POSEIDON2_WIDTH then do
        let next ← step w c0 c1 c2 s i
        let i1 ← i+1#usize
        state_only_poseidon.interpolate_three_constant_columns_loop w c0 c1 c2 next i1
      else ok s) := by
  rw [state_only_poseidon.interpolate_three_constant_columns_loop.eq_def]
  simp only [step,FJe_ThreeCell.source,bind_assoc_eq,pure_bind]
#print axioms value
#print axioms unfold_loop
end AspisR1.FJe_ThreeColumnStep
end
