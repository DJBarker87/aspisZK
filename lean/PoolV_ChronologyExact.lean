import PoolV_ChronologySuffix
set_option autoImplicit false
namespace AspisR1.PoolV_ChronologyExact
open Aeneas Aeneas.Std Result ControlFlow WP PoolV_ChronologySuffix

def Inv (new old : Slice U64) (target : Bool × Bool) (s : Usize × Bool × Bool) : Prop :=
  s.1.val ≤ min new.val.length old.val.length ∧ remaining new old s.1.val s.2.1 s.2.2 = target

theorem loop_exact (new old : Slice U64) (i : Usize) (d p : Bool)
    (bound : i.val ≤ min new.val.length old.val.length) :
    PoolV_Chronology.chronology_scan_loop new old i d p = ok (remaining new old i.val d p) := by
  let target := remaining new old i.val d p
  have h : WP.spec (PoolV_Chronology.chronology_scan_loop new old i d p) (fun out => out = target) := by
    unfold PoolV_Chronology.chronology_scan_loop
    refine loop.spec_decr_nat
      (fun s : Usize × Bool × Bool => min new.val.length old.val.length - s.1.val)
      (Inv new old target) (fun out : Bool × Bool => out = target)
      (fun (j,a,b) => PoolV_Chronology.chronology_scan_loop.body new old j a b)
      (i,d,p) ?_ ⟨bound,rfl⟩
    rintro ⟨j,a,b⟩ ⟨range,eq⟩
    dsimp only at range eq ⊢
    by_cases hn : j < Slice.len new
    · by_cases ho : j < Slice.len old
      · have vn : j.val < new.val.length := by scalar_tac
        have vo : j.val < old.val.length := by scalar_tac
        have rn : Slice.index_usize new j = ok (new.val[j.val]'vn) := by
          simp [Slice.index_usize,Slice.getElem?_Usize_eq,vn]
        have ro : Slice.index_usize old j = ok (old.val[j.val]'vo) := by
          simp [Slice.index_usize,Slice.getElem?_Usize_eq,vo]
        rw [PoolV_ChronologyStep.step new old j _ _ a b hn ho rn ro]
        change Inv new old target (Usize.wrapping_add j 1#usize,_,_) ∧
          min new.val.length old.val.length - (Usize.wrapping_add j 1#usize).val <
            min new.val.length old.val.length - j.val
        have inc := PoolV_ChronologyStep.increment new j hn
        refine ⟨⟨?_,?_⟩,?_⟩
        · simp only [inc]; omega
        · change remaining new old (Usize.wrapping_add j 1#usize).val _ _ = target
          rw [inc]
          rw [← PoolV_ChronologySuffix.next new old j.val a b vn vo]
          exact eq
        · simp only [inc]; omega
      · rw [PoolV_ChronologyStep.end_old new old j a b ho]
        change (a,b) = target
        rw [PoolV_ChronologySuffix.end_old new old j.val a b (by scalar_tac)] at eq
        exact eq
    · rw [PoolV_ChronologyStep.end_new new old j a b hn]
      change (a,b) = target
      rw [PoolV_ChronologySuffix.end_new new old j.val a b (by scalar_tac)] at eq
      exact eq
  cases run : PoolV_Chronology.chronology_scan_loop new old i d p with
  | fail e => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    rw [h]

theorem exact (new old : Slice U64) :
    PoolV_Chronology.chronology_scan new old = ok
      ((new.val.zip old.val).any (fun x => decide (x.1 < x.2)),
       (new.val.zip old.val).any (fun x => decide (x.1 > x.2))) := by
  simpa [PoolV_Chronology.chronology_scan,remaining,pairs] using
    loop_exact new old 0#usize false false (by simp)

#print axioms loop_exact
#print axioms exact
end AspisR1.PoolV_ChronologyExact
