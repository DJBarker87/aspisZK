import CurrentCallerUsizeArithmeticV1
import NDO_FIv_EqualityCell
import RPv_FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_EqualityLoop
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIv_NativeArray (value)
abbrev loop := FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value_loop

def tail (left right : Array NQ 10#usize) (start : Nat) : Nat → K
  | 0 => 1
  | n+1 => (value left start*value right start+(1-value left start)*(1-value right start))*tail left right (start+1) n

theorem exact_loop (left right : Array NQ 10#usize)
    (hl : ∀ x∈left.val,Canon x) (hr : ∀ x∈right.val,Canon x)
    (n : Nat) (index : Usize) (product out : NQ)
    (bound : index.val+n=10) (hp : Canon product)
    (run : loop left right product index=ok out) :
    Canon out ∧ decode out=decode product*tail left right index.val n := by
  induction n generalizing index product with
  | zero =>
    rw [loop,FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value_loop] at run
    simp only [lift,bind_tc_ok] at run
    have stop : ¬index<Slice.len (Array.to_slice left) := by
      have len := left.property
      scalar_tac
    rw [if_neg stop] at run
    have same := Result.ok.inj run
    subst out
    exact ⟨hp,by simp only [tail,mul_one]⟩
  | succ n ih =>
    rw [loop,FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value_loop] at run
    simp only [lift,bind_tc_ok] at run
    have more : index<Slice.len (Array.to_slice left) := by
      have len := left.property
      scalar_tac
    rw [if_pos more] at run
    obtain ⟨a,ha,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨b,hb,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨cell,hcell,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨next,hn,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨index1,hi,run⟩ := FIv_Map.bind_success _ _ _ run
    have va := FIv_NativeArray.canonical left index a hl ha
    have vb := FIv_NativeArray.canonical right index b hr hb
    have vc := FIv_EqualityCell.value a b cell va vb hcell
    have vn := FIv_NativeValue.mul product cell next hp vc.1 hn
    let nextIndex : Usize := UScalar.ofNatCore (index.val+1) (by scalar_tac)
    have add : index+1#usize=ok nextIndex := by
      apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
    have eq := Result.ok.inj (hi.symm.trans add)
    have inc : index1.val=index.val+1 := by rw [eq];rfl
    have rest := ih index1 next (by omega) vn.1 run
    refine ⟨rest.1,?_⟩
    rw [rest.2,vn.2,vc.2,← FIv_NativeArray.read left index a ha,← FIv_NativeArray.read right index b hb,inc]
    simp only [tail]
    ring

#print axioms exact_loop
end AspisR1.FIv_EqualityLoop
end
