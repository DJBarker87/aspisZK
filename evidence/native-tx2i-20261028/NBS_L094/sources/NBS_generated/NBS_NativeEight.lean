import NBS_DotTerm
set_option autoImplicit false
noncomputable section
namespace NBS_NativeEight
open Aeneas Aeneas.Std Result AspisR1 JFs_TX2_Eight
/-- Native selected-word observations at the eight product cuts. These are
local one-step observations, not a supplied final dot result. -/
def Observed (c : Array U32 8#usize) (scalar : U32)
    (before after : Array U64 8#usize) : Prop :=
  ∀ j : Fin 8,
    (after.val[j.val]'(by rw [after.property];exact j.isLt)).val=
      (before.val[j.val]'(by rw [before.property];exact j.isLt)).val+
      (c.val[j.val]'(by rw [c.property];exact j.isLt)).val*scalar.val

theorem source (c : Array U32 8#usize) (scalar : U32)
    (before after : Array U64 8#usize) (n : Nat)
    (hc : JFs_TX2_ArrayEight.Canon c) (hscalar : scalar.val<2147483647)
    (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound before n)
    (native : Observed c scalar before after) :
    JFr_TX2_DotLanes.eight c scalar before=ok after := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,rfl⟩ := JFs_TX2_ArrayEight.shape c
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := JFs_TX2_ArrayEight.shape before
  obtain ⟨o0,o1,o2,o3,o4,o5,o6,o7,rfl⟩ := JFs_TX2_ArrayEight.shape after
  simp only [JFs_TX2_ArrayEight.Canon,JFs_TX2_ArrayEight.Bound,pack,Array.make,
    List.mem_cons,List.not_mem_nil,IsEmpty.forall_iff,and_true,forall_eq_or_imp,
    forall_eq,forall_const] at hc hs
  obtain ⟨m0,m1,m2,m3,m4,m5,m6,m7,run,v,_⟩ :=
    JFs_TX2_Eight.source c0 c1 c2 c3 c4 c5 c6 c7 scalar s0 s1 s2 s3 s4 s5 s6 s7 n hc hscalar hn hs
  rcases v with ⟨v0,v1,v2,v3,v4,v5,v6,v7⟩
  have e0 : m0=o0 := UScalar.eq_of_val_eq (v0.trans (native 0).symm)
  have e1 : m1=o1 := UScalar.eq_of_val_eq (v1.trans (native 1).symm)
  have e2 : m2=o2 := UScalar.eq_of_val_eq (v2.trans (native 2).symm)
  have e3 : m3=o3 := UScalar.eq_of_val_eq (v3.trans (native 3).symm)
  have e4 : m4=o4 := UScalar.eq_of_val_eq (v4.trans (native 4).symm)
  have e5 : m5=o5 := UScalar.eq_of_val_eq (v5.trans (native 5).symm)
  have e6 : m6=o6 := UScalar.eq_of_val_eq (v6.trans (native 6).symm)
  have e7 : m7=o7 := UScalar.eq_of_val_eq (v7.trans (native 7).symm)
  simpa only [e0,e1,e2,e3,e4,e5,e6,e7] using run

#print axioms source
end NBS_NativeEight
