import RPv_FJb_M31Scalar
import RPv_FJb_ExternalExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_M31Step
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJb_TailCell (cell)
abbrev Constants := Array U32 16#usize
def Bounded (a : Constants) : Prop := ∀ i : Fin (16#usize).val,(cell a i).val < FJb_M31Scalar.P

def step (s : State) (constants : Constants) (i : Usize) : Result State := do
  let x ← Array.index_usize s i
  let c ← Array.index_usize constants i
  let m ← field.M31.add x.c0.a c
  let (x1,back) ← Array.index_mut_usize s i
  let s1 := back (FJb_M31Scalar.updated x1 m)
  let x2 ← Array.index_usize s1 i
  let r ← state_only_poseidon.pow5 x2
  Array.update s1 i r

theorem value (s out : State) (constants : Constants) (i : Usize)
    (hi : i.val < (16#usize).val) (hs : canonical s) (hc : Bounded constants)
    (run : step s constants i=ok out) :
    canonical out ∧ decoded out=Function.update (decoded s) ⟨i.val,hi⟩
      ((decoded s ⟨i.val,hi⟩+((cell constants ⟨i.val,hi⟩).val : K))^5) := by
  unfold step at run
  obtain ⟨x,hx,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨c,hc0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨m,hm,run⟩ := FIv_Map.bind_success _ _ _ run
  have hmut : Array.index_mut_usize s i=ok (x,fun z=>s.set i z) := by
    simp only [Array.index_mut_usize,hx,bind_tc_ok]
  rw [hmut,bind_tc_ok] at run
  let u := FJb_M31Scalar.updated x m
  let s1 := s.set i u
  change (do
    let x2 ← Array.index_usize s1 i
    let r ← state_only_poseidon.pow5 x2
    Array.update s1 i r)=ok out at run
  have readAgain : Array.index_usize s1 i=ok u := by
    rw [RawPoseidonExternalRowReads.array_index_usize_ok s1 i hi]
    congr 1
    change (s.val.set i.val u)[i.val]'_=u
    exact List.getElem_set_self (by simpa only [List.length_set,s.property] using hi)
  rw [readAgain,bind_tc_ok] at run
  obtain ⟨r,hr,run⟩ := FIv_Map.bind_success _ _ _ run
  have hc1 : Array.index_usize constants i=ok (cell constants ⟨i.val,hi⟩) :=
    RawPoseidonExternalRowReads.array_index_usize_ok constants i hi
  have ec : c=cell constants ⟨i.val,hi⟩ := Result.ok.inj (hc0.symm.trans hc1)
  have cb : c.val < FJb_M31Scalar.P := by rw [ec];exact hc _
  have source : FJb_M31Scalar.source x c=ok r := by
    unfold FJb_M31Scalar.source
    rw [hm,bind_tc_ok]
    exact hr
  have vr := FJb_M31Scalar.value x r c (FIv_NativeArray.canonical s i x hs hx) cb source
  obtain ⟨next,un,uset⟩ := WP.spec_imp_exists
    (Array.update_spec s1 i r (by simpa only [s1.property] using hi))
  rw [uset] at un
  have overwrite : s1.set i r=s.set i r := by
    apply Subtype.ext
    simp only [s1,Array.set_val_eq,List.set_set]
  rw [overwrite] at un
  have eo : s.set i r=out := Result.ok.inj (un.symm.trans run)
  subst out
  obtain ⟨original,uo,oset⟩ := WP.spec_imp_exists
    (Array.update_spec s i r (by simpa only [s.property] using hi))
  rw [oset] at uo
  have vo := FIw_ArrayValue.update s (s.set i r) i r hi hs vr.1 uo
  refine ⟨vo.1,?_⟩
  rw [vo.2,vr.2,FIw_ArrayReadValue.read s i hi x hx,ec]
#print axioms value
end AspisR1.FJb_M31Step
end
