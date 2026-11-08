import NNG_SelectedAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SelectAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem index {A : Type} (s : Slice A) (i : Usize) (h : i.val < s.val.length) :
 Slice.index_usize s i=ok (s.val[i.val]'h) := by
 obtain ⟨x,returned,value⟩ := WP.spec_imp_exists (Slice.index_usize_spec s i h)
 exact returned.trans (congrArg Result.ok value)
#print axioms index

theorem source {W : Type} (s : Parent W) (env : RSL.Env) (p pub ck : Account)
 (accounts : s.accounts.val=[p,pub,ck]) (route : s.data.val.length=2) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_Tree345.select (NNG_Calls345.calls env) s)=
 NNG_Phases345.bodyRun LIB_Instances.VL LIB_Instances.C (fun _=>true) NNG_Producer328.producer
 (NNG_ProjectFrames345.selected ⟨s,p,pub,ck⟩) env := by
 have a0 : Slice.index_usize s.accounts 0#usize=ok p := by
  rw [index s.accounts 0#usize (by rw [accounts];decide)]
  simp only [accounts,List.getElem_cons_zero]
 have a1 : Slice.index_usize s.accounts 1#usize=ok pub := by
  rw [index s.accounts 1#usize (by rw [accounts];decide)]
  simp only [accounts,List.getElem_cons_succ,List.getElem_cons_zero]
 have a2 : Slice.index_usize s.accounts 2#usize=ok ck := by
  rw [index s.accounts 2#usize (by rw [accounts];decide)]
  simp only [accounts,List.getElem_cons_succ,List.getElem_cons_zero]
 unfold NNG_Tree345.select
 rw [a0,a1,a2]
 exact NNG_SelectedAssociation345.source ⟨s,p,pub,ck⟩ env route
#print axioms source
end AspisR1.NNG_SelectAssociation345
