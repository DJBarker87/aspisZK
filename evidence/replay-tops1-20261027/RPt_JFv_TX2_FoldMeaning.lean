import RPt_JFv_TX2_ArrayMeaning
import RPt_JFs_TX2_FoldEight
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_FoldMeaning
open Aeneas Aeneas.Std Result JFs_TX2_Eight
open JFv_TX2_ArrayMeaning (cell)

theorem source (sums limbs : Array U64 8#usize) (n : Nat) (hn : n<7)
    (hs : JFs_TX2_FoldEight.Bound limbs n) :
    ∃ out, JFs_TX2_FoldEight.eight sums limbs=ok out ∧
      JFs_TX2_FoldEight.Bound out (n+1) ∧
      ∀ j : Fin 8, (cell out j).val=(cell limbs j).val+(FIo_ReduceBounds.fold (cell sums j)).val := by
  obtain ⟨out,run,bound⟩ := JFs_TX2_FoldEight.source sums limbs n hn hs
  refine ⟨out,run,bound,?_⟩
  obtain ⟨x0,x1,x2,x3,x4,x5,x6,x7,rfl⟩ := JFs_TX2_ArrayEight.shape sums
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := JFs_TX2_ArrayEight.shape limbs
  simp only [JFs_TX2_FoldEight.Bound,pack,Array.make,List.mem_cons,List.not_mem_nil,
    IsEmpty.forall_iff,and_true,forall_eq_or_imp,forall_const] at hs
  rcases hs with ⟨hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7⟩
  obtain ⟨o0,h0,v0,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack s0 s1 s2 s3 s4 s5 s6 s7) 0#usize x0 s0 n hn (by decide) rfl rfl hs0
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 s1 s2 s3 s4 s5 s6 s7) at h0
  obtain ⟨o1,h1,v1,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 s1 s2 s3 s4 s5 s6 s7) 1#usize x1 s1 n hn (by decide) rfl rfl hs1
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 s2 s3 s4 s5 s6 s7) at h1
  obtain ⟨o2,h2,v2,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 s2 s3 s4 s5 s6 s7) 2#usize x2 s2 n hn (by decide) rfl rfl hs2
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 s3 s4 s5 s6 s7) at h2
  obtain ⟨o3,h3,v3,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 s3 s4 s5 s6 s7) 3#usize x3 s3 n hn (by decide) rfl rfl hs3
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 s4 s5 s6 s7) at h3
  obtain ⟨o4,h4,v4,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 s4 s5 s6 s7) 4#usize x4 s4 n hn (by decide) rfl rfl hs4
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 s5 s6 s7) at h4
  obtain ⟨o5,h5,v5,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 o4 s5 s6 s7) 5#usize x5 s5 n hn (by decide) rfl rfl hs5
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 o5 s6 s7) at h5
  obtain ⟨o6,h6,v6,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 o4 o5 s6 s7) 6#usize x6 s6 n hn (by decide) rfl rfl hs6
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 o5 o6 s7) at h6
  obtain ⟨o7,h7,v7,_⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 o4 o5 o6 s7) 7#usize x7 s7 n hn (by decide) rfl rfl hs7
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 o5 o6 o7) at h7
  have run1 : JFs_TX2_FoldEight.eight (pack x0 x1 x2 x3 x4 x5 x6 x7)
      (pack s0 s1 s2 s3 s4 s5 s6 s7)=ok (pack o0 o1 o2 o3 o4 o5 o6 o7) := by
    simp only [JFs_TX2_FoldEight.eight,h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]
  have same : out=pack o0 o1 o2 o3 o4 o5 o6 o7 := Result.ok.inj (run.symm.trans run1)
  subst out
  intro j
  fin_cases j
  · exact v0
  · exact v1
  · exact v2
  · exact v3
  · exact v4
  · exact v5
  · exact v6
  · exact v7
#print axioms source
end AspisR1.JFv_TX2_FoldMeaning
end
