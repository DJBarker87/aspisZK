import RPt_JFs_TX2_Eight
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_ArrayEight
open Aeneas Aeneas.Std Result
open JFs_TX2_Eight

theorem shape {α : Type} (a : Array α 8#usize) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, a=pack a0 a1 a2 a3 a4 a5 a6 a7 := by
  rcases a with ⟨xs,h⟩
  change xs.length=8 at h
  cases xs with
  | nil => simp at h
  | cons a0 xs =>
    cases xs with
    | nil => simp at h
    | cons a1 xs =>
      cases xs with
      | nil => simp at h
      | cons a2 xs =>
        cases xs with
        | nil => simp at h
        | cons a3 xs =>
          cases xs with
          | nil => simp at h
          | cons a4 xs =>
            cases xs with
            | nil => simp at h
            | cons a5 xs =>
              cases xs with
              | nil => simp at h
              | cons a6 xs =>
                cases xs with
                | nil => simp at h
                | cons a7 xs =>
                  cases xs with
                  | nil => exact ⟨a0,a1,a2,a3,a4,a5,a6,a7,rfl⟩
                  | cons a8 xs => simp at h

def Canon (a : Array U32 8#usize) : Prop := ∀ x∈a.val,x.val<JFr_TX2_DotBounds.P
def Bound (a : Array U64 8#usize) (n : Nat) : Prop :=
  ∀ x∈a.val,x.val≤n*((JFr_TX2_DotBounds.P-1)*(JFr_TX2_DotBounds.P-1))

theorem source (c : Array U32 8#usize) (scalar : U32)
    (s : Array U64 8#usize) (n : Nat) (hc : Canon c)
    (hscalar : scalar.val<JFr_TX2_DotBounds.P) (hn : n<4) (hs : Bound s n) :
    ∃ out, JFr_TX2_DotLanes.eight c scalar s=ok out ∧ Bound out (n+1) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,rfl⟩ := shape c
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := shape s
  simp only [Canon,Bound,pack,Array.make,List.mem_cons,List.not_mem_nil,IsEmpty.forall_iff,and_true,
    forall_eq_or_imp,forall_eq,forall_const] at hc hs
  obtain ⟨o0,o1,o2,o3,o4,o5,o6,o7,run,_,bounds⟩ :=
    JFs_TX2_Eight.source c0 c1 c2 c3 c4 c5 c6 c7 scalar s0 s1 s2 s3 s4 s5 s6 s7 n
      hc hscalar hn hs
  refine ⟨pack o0 o1 o2 o3 o4 o5 o6 o7,run,?_⟩
  simpa only [Bound,pack,Array.make,List.mem_cons,List.not_mem_nil,IsEmpty.forall_iff,and_true,
    forall_eq_or_imp,forall_eq,forall_const] using bounds

#print axioms shape
#print axioms source
end AspisR1.JFs_TX2_ArrayEight
end
