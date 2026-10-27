import RPv_FJb_LimbMeaning
import RPv_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_MatrixGroupStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
abbrev State := Array NQ 16#usize
def inputs (s : State) (i0 i1 i2 i3 : Usize) (k : Fin (4#usize).val) : K :=
  match k.val with
  | 0 => FIv_NativeArray.value s i0.val
  | 1 => FIv_NativeArray.value s i1.val
  | 2 => FIv_NativeArray.value s i2.val
  | _ => FIv_NativeArray.value s i3.val

def step (s : State) (i0 i1 i2 i3 : Usize) : Result State := do
  let x0 ← Array.index_usize s i0
  let x1 ← Array.index_usize s i1
  let x2 ← Array.index_usize s i2
  let x3 ← Array.index_usize s i3
  let raw ← FIq_Native.core.array.Array.map (BuiltinFnMut NQ (Array U32 4#usize))
    (Array.make 4#usize [x0,x1,x2,x3]) state_only_poseidon.extension_limbs
  let y0 ← state_only_poseidon.external_linear_lazy_row raw 0#usize
  let s0 ← Array.update s i0 y0
  let y1 ← state_only_poseidon.external_linear_lazy_row raw 1#usize
  let s1 ← Array.update s0 i1 y1
  let y2 ← state_only_poseidon.external_linear_lazy_row raw 2#usize
  let s2 ← Array.update s1 i2 y2
  let y3 ← state_only_poseidon.external_linear_lazy_row raw 3#usize
  Array.update s2 i3 y3

def model (s : State) (i0 i1 i2 i3 : Usize)
    (h0 : i0.val < (16#usize).val) (h1 : i1.val < (16#usize).val)
    (h2 : i2.val < (16#usize).val) (h3 : i3.val < (16#usize).val) :
    Fin (16#usize).val → K :=
  let rows := R0P.poseidonMat4 (inputs s i0 i1 i2 i3)
  Function.update (Function.update (Function.update (Function.update
    (decoded s) ⟨i0.val,h0⟩ (rows 0)) ⟨i1.val,h1⟩ (rows 1))
    ⟨i2.val,h2⟩ (rows 2)) ⟨i3.val,h3⟩ (rows 3)

theorem value (s out : State) (i0 i1 i2 i3 : Usize)
    (h0 : i0.val < (16#usize).val) (h1 : i1.val < (16#usize).val)
    (h2 : i2.val < (16#usize).val) (h3 : i3.val < (16#usize).val)
    (hs : canonical s) (run : step s i0 i1 i2 i3=ok out) :
    canonical out ∧ decoded out=model s i0 i1 i2 i3 h0 h1 h2 h3 := by
  unfold step at run
  obtain ⟨x0,hx0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨x1,hx1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨x2,hx2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨x3,hx3,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨raw,hr,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨y0,hy0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨s0,hs0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨y1,hy1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨s1,hs1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨y2,hy2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨s2,hs2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨y3,hy3,run⟩ := FIv_Map.bind_success _ _ _ run
  let a := Array.make 4#usize [x0,x1,x2,x3]
  have v0 := FJb_LimbMeaning.value a raw 0#usize (by decide) y0 hr hy0
  have v1 := FJb_LimbMeaning.value a raw 1#usize (by decide) y1 hr hy1
  have v2 := FJb_LimbMeaning.value a raw 2#usize (by decide) y2 hr hy2
  have v3 := FJb_LimbMeaning.value a raw 3#usize (by decide) y3 hr hy3
  have u0 := FIw_ArrayValue.update s s0 i0 y0 h0 hs v0.1 hs0
  have u1 := FIw_ArrayValue.update s0 s1 i1 y1 h1 u0.1 v1.1 hs1
  have u2 := FIw_ArrayValue.update s1 s2 i2 y2 h2 u1.1 v2.1 hs2
  have u3 := FIw_ArrayValue.update s2 out i3 y3 h3 u2.1 v3.1 run
  have he : decoded a=inputs s i0 i1 i2 i3 := by
    funext k
    fin_cases k <;>
      simp only [a,decoded,FIw_ArrayValue.cells,Array.make,inputs]
    · exact (FIv_NativeArray.read s i0 x0 hx0).symm
    · exact (FIv_NativeArray.read s i1 x1 hx1).symm
    · exact (FIv_NativeArray.read s i2 x2 hx2).symm
    · exact (FIv_NativeArray.read s i3 x3 hx3).symm
  refine ⟨u3.1,?_⟩
  rw [u3.2,u2.2,u1.2,u0.2,v0.2,v1.2,v2.2,v3.2,he]
  rfl
#print axioms value
end AspisR1.FJb_MatrixGroupStep
end
