import JFs_TX2_ArrayEight
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_ArrayMeaning
open Aeneas Aeneas.Std Result JFs_TX2_Eight

def cell {α : Type} (a : Array α 8#usize) (j : Fin 8) : α :=
  a.val[j.val]'(by rw [a.property];exact j.isLt)

theorem source (c : Array U32 8#usize) (scalar : U32) (s : Array U64 8#usize)
    (n : Nat) (hc : JFs_TX2_ArrayEight.Canon c) (hscalar : scalar.val<P)
    (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound s n) :
    ∃ out, JFr_TX2_DotLanes.eight c scalar s=ok out ∧
      JFs_TX2_ArrayEight.Bound out (n+1) ∧
      ∀ j : Fin 8, (cell out j).val=(cell s j).val+(cell c j).val*scalar.val := by
  obtain ⟨out,run,bound⟩ := JFs_TX2_ArrayEight.source c scalar s n hc hscalar hn hs
  refine ⟨out,run,bound,?_⟩
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,rfl⟩ := JFs_TX2_ArrayEight.shape c
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := JFs_TX2_ArrayEight.shape s
  simp only [JFs_TX2_ArrayEight.Canon,JFs_TX2_ArrayEight.Bound,pack,Array.make,
    List.mem_cons,List.not_mem_nil,IsEmpty.forall_iff,and_true,
    forall_eq_or_imp,forall_eq,forall_const] at hc hs
  obtain ⟨o0,o1,o2,o3,o4,o5,o6,o7,run1,values,_⟩ := JFs_TX2_Eight.source
    c0 c1 c2 c3 c4 c5 c6 c7 scalar s0 s1 s2 s3 s4 s5 s6 s7 n hc hscalar hn hs
  have same : out=pack o0 o1 o2 o3 o4 o5 o6 o7 := Result.ok.inj (run.symm.trans run1)
  subst out
  intro j
  fin_cases j
  · exact values.1
  · exact values.2.1
  · exact values.2.2.1
  · exact values.2.2.2.1
  · exact values.2.2.2.2.1
  · exact values.2.2.2.2.2.1
  · exact values.2.2.2.2.2.2.1
  · exact values.2.2.2.2.2.2.2
#print axioms source
end AspisR1.JFv_TX2_ArrayMeaning
end
