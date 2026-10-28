import PV_B3P_MaskScan132
namespace PV_B3P_MaskOuter132
open Aeneas Aeneas.Std PV_B3P_132 PV_B3P_MaskPrefix132 PV_B3P_MaskScan132
set_option autoImplicit false

theorem outer (p : Nat → Nat → Bool)
    (hp : ∀ (r c : Usize), r.val < 1024 → c.val < 16 →
      reference132.free r c = .ok (p r.val c.val))
    (n : Nat) (out : Array reference132.Cell 3803#usize) (count c : Usize)
    (hc : c.val+n = 16)
    (hcap : count.val + (columns p c.val n).length ≤ 3803) :
    ∃ out' count', reference132.cells_loop0 out count c = .ok (out',count') ∧
      count'.val = count.val + (columns p c.val n).length ∧
      written out' count'.val = written out count.val ++ columns p c.val n := by
  induction n generalizing out count c with
  | zero =>
    have hd := PV_B3P_MaskStep132.outer_done out count c (by omega)
    refine ⟨out,count,?_,by simp [columns],by simp [columns]⟩
    unfold reference132.cells_loop0
    rw [loop.eq_1]
    dsimp only
    rw [hd]
  | succ n ih =>
    have hcol : c.val < 16 := by omega
    have hnext := (PV_B3P_MaskLoopBounds132.column_next c hcol).1
    have hinner : count.val + (rows p c.val 0 1024).length ≤ 3803 := by
      simp only [columns,List.length_append] at hcap
      omega
    obtain ⟨o,k,hloop,hcount,hprefix⟩ := inner p hp 1024 out count c 0#usize (by simp) hcol hinner
    have hcap' : k.val + (columns p (Usize.wrapping_add c 1#usize).val n).length ≤ 3803 := by
      simp only [columns,List.length_append] at hcap
      rw [hcount,hnext]
      omega
    obtain ⟨o',k',hloop',hcount',hprefix'⟩ := ih o k (Usize.wrapping_add c 1#usize) (by omega) hcap'
    have hs : reference132.cells_loop0.body out count c =
        .ok (.cont (o,k,Usize.wrapping_add c 1#usize)) := by
      have h : c < 16#usize := by scalar_tac
      simp only [reference132.cells_loop0.body,h,↓reduceIte,hloop,lift,bind_tc_ok]
    refine ⟨o',k',?_,?_,?_⟩
    · unfold reference132.cells_loop0 at hloop' ⊢
      rw [loop.eq_1]
      dsimp only
      rw [hs]
      exact hloop'
    · simp only [columns,List.length_append]
      rw [hcount,hnext] at hcount'
      omega
    · rw [hprefix,hnext] at hprefix'
      simpa only [columns,List.append_assoc] using hprefix'

#print axioms outer
end PV_B3P_MaskOuter132
