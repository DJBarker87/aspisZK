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
 rcases s with ⟨program,accts,data,world,events⟩
 rcases accts with ⟨xs,bound⟩
 change xs=[p,pub,ck] at accounts
 subst xs
 exact NNG_SelectedAssociation345.source
  ⟨⟨program,⟨[p,pub,ck],bound⟩,data,world,events⟩,p,pub,ck⟩ env route
#print axioms source
end AspisR1.NNG_SelectAssociation345
