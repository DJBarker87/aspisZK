import PV_B3P_MaskPrefix132
namespace PV_B3P_MaskScan132
open Aeneas Aeneas.Std PV_B3P_132 PV_B3P_MaskPrefix132
set_option autoImplicit false

def rows (p : Nat → Nat → Bool) (c r : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 => (if p r c then [(r,c)] else []) ++ rows p c (r+1) n

def columns (p : Nat → Nat → Bool) (c : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 => rows p c 0 1024 ++ columns p (c+1) n

theorem inner (p : Nat → Nat → Bool)
    (hp : ∀ (r c : Usize), r.val < 1024 → c.val < 16 →
      reference132.free r c = .ok (p r.val c.val))
    (n : Nat) (out : Array reference132.Cell 3803#usize) (count c r : Usize)
    (hr : r.val+n = 1024) (hc : c.val < 16)
    (hcap : count.val + (rows p c.val r.val n).length ≤ 3803) :
    ∃ out' count', reference132.cells_loop0_loop0 out count c r = .ok (out',count') ∧
      count'.val = count.val + (rows p c.val r.val n).length ∧
      written out' count'.val = written out count.val ++ rows p c.val r.val n := by
  induction n generalizing out count r with
  | zero =>
    have hd := PV_B3P_MaskStep132.inner_done out count r c (by omega)
    refine ⟨out,count,?_,by simp [rows],by simp [rows]⟩
    unfold reference132.cells_loop0_loop0
    rw [loop.eq_1,hd]
  | succ n ih =>
    have hrow : r.val < 1024 := by omega
    have hnext := (PV_B3P_MaskLoopBounds132.row_next r hrow).1
    have hfree := hp r c hrow hc
    cases hb : p r.val c.val with
    | false =>
      have hstep := PV_B3P_MaskStep132.skip out count r c hrow (by simpa [hb] using hfree)
      have hcap' : count.val + (rows p c.val (Usize.wrapping_add r 1#usize).val n).length ≤ 3803 := by
        simpa [rows,hb,hnext] using hcap
      obtain ⟨o,k,hloop,hcount,hprefix⟩ := ih out count (Usize.wrapping_add r 1#usize) (by omega) hcap'
      refine ⟨o,k,?_,?_,?_⟩
      · unfold reference132.cells_loop0_loop0 at hloop ⊢
        rw [loop.eq_1,hstep]
        exact hloop
      · simpa [rows,hb,hnext] using hcount
      · simpa [rows,hb,hnext] using hprefix
    | true =>
      have hn : count.val < 3803 := by
        simp only [rows,hb,↓reduceIte,List.length_append,List.length_singleton] at hcap
        omega
      obtain ⟨o,hs,ho⟩ := PV_B3P_MaskStep132.write_retained out count r c hrow hn (by simpa [hb] using hfree)
      have hk := (PV_B3P_MaskLoopBounds132.count_next count hn).1
      have hcap' : (Usize.wrapping_add count 1#usize).val +
          (rows p c.val (Usize.wrapping_add r 1#usize).val n).length ≤ 3803 := by
        simp only [rows,hb,↓reduceIte,List.length_append,List.length_singleton] at hcap
        rw [hk,hnext]
        omega
      obtain ⟨o',k,hloop,hcount,hprefix⟩ := ih o (Usize.wrapping_add count 1#usize)
        (Usize.wrapping_add r 1#usize) (by omega) hcap'
      refine ⟨o',k,?_,?_,?_⟩
      · unfold reference132.cells_loop0_loop0 at hloop ⊢
        rw [loop.eq_1,hs]
        exact hloop
      · simp only [rows,hb,↓reduceIte,List.length_append,List.length_singleton]
        rw [hk,hnext] at hcount
        omega
      · rw [ho,hk,write_prefix out count r c hn hrow hc,hnext] at hprefix
        simpa only [rows,hb,↓reduceIte,List.append_assoc] using hprefix

#print axioms inner
end PV_B3P_MaskScan132
