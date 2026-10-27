import FJe_LocalPackedValue
import FJb_MatrixModel
import FJb_GroupIndices
import FJe_ExternalAdjoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedGroupStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State inputs)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
abbrev Packed := Array NQ 4#usize
def localModel (s : State) (g : Fin 4) : K :=
  R0P.poseidonPackingFormula iBasis uBasis
    (R0P.poseidonMat4 (FJb_MatrixBlock.input s g.val))
def atIndices (s : State) (p : Packed) (g i0 i1 i2 i3 : Usize) : Result Packed := do
  let x0 ← Array.index_usize s i0
  let x1 ← Array.index_usize s i1
  let x2 ← Array.index_usize s i2
  let x3 ← Array.index_usize s i3
  let q ← state_only_poseidon.external_local_packed (Array.make 4#usize [x0,x1,x2,x3])
  Array.update p g q

def step (s : State) (p : Packed) (g : Usize) : Result Packed := do
  let i0 ← 4#usize*g
  let x0 ← Array.index_usize s i0
  let i1 ← i0+1#usize
  let x1 ← Array.index_usize s i1
  let i2 ← i0+2#usize
  let x2 ← Array.index_usize s i2
  let i3 ← i0+3#usize
  let x3 ← Array.index_usize s i3
  let q ← state_only_poseidon.external_local_packed (Array.make 4#usize [x0,x1,x2,x3])
  Array.update p g q

theorem factor (s : State) (p : Packed) (g i0 i1 i2 i3 : Usize)
    (h0 : (4#usize*g : Result Usize)=ok i0)
    (h1 : (i0+1#usize : Result Usize)=ok i1)
    (h2 : (i0+2#usize : Result Usize)=ok i2)
    (h3 : (i0+3#usize : Result Usize)=ok i3) :
    step s p g=atIndices s p g i0 i1 i2 i3 := by
  simp only [step,atIndices,h0,h1,h2,h3,bind_tc_ok]

theorem value (s : State) (p out : Packed) (g : Usize) (hg : g.val<4)
    (hs : canonical s) (hp : canonical p) (run : step s p g=ok out) :
    canonical out ∧ decoded out=Function.update (decoded p) ⟨g.val,hg⟩
      (localModel s ⟨g.val,hg⟩) := by
  obtain ⟨i0,i1,i2,i3,next,h0,v0,h1,v1,h2,v2,h3,v3,_,_⟩ := FJb_GroupIndices.value g hg
  rw [factor s p g i0 i1 i2 i3 h0 h1 h2 h3] at run
  unfold atIndices at run
  obtain ⟨x0,r0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨x1,r1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨x2,r2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨x3,r3,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q,rq,run⟩ := FIv_Map.bind_success _ _ _ run
  let a := Array.make 4#usize [x0,x1,x2,x3]
  have ca : canonical a := by
    intro x hx
    simp only [a,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact FIv_NativeArray.canonical s i0 _ hs r0
    · exact FIv_NativeArray.canonical s i1 _ hs r1
    · exact FIv_NativeArray.canonical s i2 _ hs r2
    · exact FIv_NativeArray.canonical s i3 _ hs r3
  have va := FJe_LocalPackedValue.value a q ca rq
  have vu := FIw_ArrayValue.update p out g q hg hp va.1 run
  have ea : decoded a=inputs s i0 i1 i2 i3 := by
    funext k
    fin_cases k <;> simp only [a,decoded,FIw_ArrayValue.cells,Array.make,inputs]
    · exact (FIv_NativeArray.read s i0 x0 r0).symm
    · exact (FIv_NativeArray.read s i1 x1 r1).symm
    · exact (FIv_NativeArray.read s i2 x2 r2).symm
    · exact (FIv_NativeArray.read s i3 x3 r3).symm
  have ei : inputs s i0 i1 i2 i3=FJb_MatrixBlock.input s g.val := by
    funext k
    fin_cases k <;> simp only [inputs,FJb_MatrixBlock.input,v0,v1,v2,v3,Nat.add_zero]
  refine ⟨vu.1,vu.2.trans ?_⟩
  apply congrArg (Function.update (decoded p) (⟨g.val,hg⟩ : Fin (4#usize).val))
  exact va.2.trans (congrArg (fun f=>R0P.poseidonPackingFormula iBasis uBasis
    (R0P.poseidonMat4 f)) (ea.trans ei))

theorem unfold_loop (s : State) (p : Packed) (g : Usize) :
    state_only_poseidon.external_linear_packed_loop s p g=
      (if g<4#usize then do
        let next ← step s p g
        let g1 ← g+1#usize
        state_only_poseidon.external_linear_packed_loop s next g1
      else ok p) := by
  rw [state_only_poseidon.external_linear_packed_loop.eq_def]
  simp only [step,bind_assoc_eq]
#print axioms factor
#print axioms value
#print axioms unfold_loop
end AspisR1.FJe_PackedGroupStep
end
