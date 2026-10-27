import RPu_JGa_PatternBounds
import RPu_JGa_ArrayProperty
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_PatternCell
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

def run (a powers : Array field.QM31 16#usize) (i : Usize)
    (p : CompiledPoolV1PairForestPattern) (value : field.QM31) : Result field.QM31 := do
  let kind ← Array.index_usize p.kinds i
  if kind=1#u8 then do
    let column ← Array.index_usize p.columns i
    let index ← lift (core.convert.num.FromUsizeU8.from column)
    let q ← Array.index_usize a index
    let offset ← Array.index_usize p.offsets i
    let q1 ← lift_m31 offset
    let source ← field.QM31.add q q1
    let q2 ← Array.index_usize powers i
    let q3 ← field.QM31.mul q2 source
    field.QM31.add value q3
  else ok value

@[step] theorem source (a powers : Array field.QM31 16#usize) (i : Usize)
    (p : CompiledPoolV1PairForestPattern) (value : field.QM31) (hi : i.val<16)
    (ha : canonical a) (hp : canonical powers) (hv : Canon value) (hg : JGa_PatternBounds.Good p) :
    run a powers i p value ⦃ out => Canon out ⦄ := by
  obtain ⟨kind,hk,_⟩ := WP.spec_imp_exists (JGa_ArrayProperty.read p.kinds i (fun _=>True) hi (by simp))
  unfold run
  rw [hk,bind_tc_ok]
  split
  · obtain ⟨column,hc,hcv⟩ := WP.spec_imp_exists (JGa_ArrayProperty.read p.columns i (fun x=>x.val<16) hi hg.1)
    obtain ⟨offset,ho,hov⟩ := WP.spec_imp_exists (JGa_ArrayProperty.read p.offsets i (fun x=>x.val<2147483647) hi hg.2)
    rw [hc,bind_tc_ok,ho]
    simp only [lift,bind_tc_ok]
    have cv := core.convert.num.FromUsizeU8.from_val_eq column
    step* <;> first | assumption | scalar_tac
  · exact hv
#print axioms source
end AspisR1.JGa_PatternCell
end
