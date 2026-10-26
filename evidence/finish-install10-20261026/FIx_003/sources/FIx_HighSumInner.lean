import FIx_ArithmeticTotal
import FIv_NativeArray
import FIq_Native10
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_HighSumInner
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Range := core.ops.range.Range Usize
abbrev loop := pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0

def model (s : Selectors) : Nat → Nat → K → K
  | 0,_,acc => acc
  | n+1,i,acc => model s n (i+1) (acc+FIv_NativeArray.value s.high i)

theorem read {N : Usize} (a : Array NQ N) (i : Usize) (hi : i.val<N.val)
    (hc : ∀ x∈a.val,Canon x) :
    ∃ x,Array.index_usize a i=ok x ∧ Canon x ∧ decode x=FIv_NativeArray.value a i.val := by
  let x := a.val[i.val]'(by simpa only [a.property] using hi)
  have hidx : Array.index_usize a i=ok x := by
    have bound : i.val<a.val.length := by simpa only [a.property] using hi
    unfold Array.index_usize
    change (match a.val[i.val]? with | none => _ | some y => ok y)=ok x
    rw [List.getElem?_eq_getElem bound]
  exact ⟨x,hidx,FIv_NativeArray.canonical a i x hc hidx,(FIv_NativeArray.read a i x hidx).symm⟩

theorem value (n : Nat) (iter : Range) (s : Selectors) (acc : NQ)
    (hend : iter.end.val≤64) (hspan : iter.start.val+n=iter.end.val)
    (hh : ∀ x∈s.high.val,Canon x) (ha : Canon acc) :
    ∃ out,loop iter s acc=ok (s,out) ∧ Canon out ∧
      decode out=model s n iter.start.val (decode acc) := by
  induction n generalizing iter acc with
  | zero =>
    refine ⟨acc,?_,ha,rfl⟩
    rw [loop,pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0]
    simp only [OccupancyRangeTraversal.next_done iter (by omega),bind_tc_ok]
    rfl
  | succ n ih =>
    obtain ⟨iter1,hn,hs,he,hb⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    obtain ⟨q,hq,hcq,hvq⟩ := read s.high iter.start (by simpa using (show iter.start.val<64 by omega)) hh
    obtain ⟨next,ha1,hca,hva⟩ := FIx_ArithmeticTotal.add acc q ha hcq
    obtain ⟨out,hr,hco,hvo⟩ := ih iter1 next (by simpa only [he] using hend) (by rw [he,hs];omega) hca
    refine ⟨out,?_,hco,?_⟩
    · rw [loop,pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0]
      simp only [hn,bind_tc_ok]
      dsimp only
      rw [hq,bind_tc_ok,ha1,bind_tc_ok]
      exact hr
    · rw [hvo,hs,hva,hvq]
      rfl
#print axioms read
#print axioms value
end AspisR1.FIx_HighSumInner
end
