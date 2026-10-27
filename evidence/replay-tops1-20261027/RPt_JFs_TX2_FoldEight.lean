import RPt_JFs_TX2_FoldLane
import RPt_JFs_TX2_ArrayEight
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_FoldEight
open Aeneas Aeneas.Std Result
open JFs_TX2_Eight
def Bound (a : Array U64 8#usize) (n : Nat) : Prop :=
  ∀ x∈a.val,x.val≤n*JFs_TX2_FoldLane.R
def eight (sums limbs : Array U64 8#usize) : Result (Array U64 8#usize) := do
  let l1 ← JFs_TX2_FoldLane.lane sums limbs 0#usize
  let l2 ← JFs_TX2_FoldLane.lane sums l1 1#usize
  let l3 ← JFs_TX2_FoldLane.lane sums l2 2#usize
  let l4 ← JFs_TX2_FoldLane.lane sums l3 3#usize
  let l5 ← JFs_TX2_FoldLane.lane sums l4 4#usize
  let l6 ← JFs_TX2_FoldLane.lane sums l5 5#usize
  let l7 ← JFs_TX2_FoldLane.lane sums l6 6#usize
  let l8 ← JFs_TX2_FoldLane.lane sums l7 7#usize
  ok l8

theorem packed (x0 x1 x2 x3 x4 x5 x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 : U64)
    (n : Nat) (hn : n<7)
    (hs : s0.val≤n*JFs_TX2_FoldLane.R ∧ s1.val≤n*JFs_TX2_FoldLane.R ∧ s2.val≤n*JFs_TX2_FoldLane.R ∧ s3.val≤n*JFs_TX2_FoldLane.R ∧ s4.val≤n*JFs_TX2_FoldLane.R ∧ s5.val≤n*JFs_TX2_FoldLane.R ∧ s6.val≤n*JFs_TX2_FoldLane.R ∧ s7.val≤n*JFs_TX2_FoldLane.R) :
    ∃ o0 o1 o2 o3 o4 o5 o6 o7 : U64,
      eight (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack s0 s1 s2 s3 s4 s5 s6 s7)=
        ok (pack o0 o1 o2 o3 o4 o5 o6 o7) ∧
      (o0.val≤(n+1)*JFs_TX2_FoldLane.R ∧ o1.val≤(n+1)*JFs_TX2_FoldLane.R ∧ o2.val≤(n+1)*JFs_TX2_FoldLane.R ∧ o3.val≤(n+1)*JFs_TX2_FoldLane.R ∧ o4.val≤(n+1)*JFs_TX2_FoldLane.R ∧ o5.val≤(n+1)*JFs_TX2_FoldLane.R ∧ o6.val≤(n+1)*JFs_TX2_FoldLane.R ∧ o7.val≤(n+1)*JFs_TX2_FoldLane.R) := by
  rcases hs with ⟨hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7⟩
  obtain ⟨o0,h0,_,b0⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack s0 s1 s2 s3 s4 s5 s6 s7) 0#usize x0 s0 n hn (by decide) rfl rfl hs0
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 s1 s2 s3 s4 s5 s6 s7) at h0
  obtain ⟨o1,h1,_,b1⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 s1 s2 s3 s4 s5 s6 s7) 1#usize x1 s1 n hn (by decide) rfl rfl hs1
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 s2 s3 s4 s5 s6 s7) at h1
  obtain ⟨o2,h2,_,b2⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 s2 s3 s4 s5 s6 s7) 2#usize x2 s2 n hn (by decide) rfl rfl hs2
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 s3 s4 s5 s6 s7) at h2
  obtain ⟨o3,h3,_,b3⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 s3 s4 s5 s6 s7) 3#usize x3 s3 n hn (by decide) rfl rfl hs3
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 s4 s5 s6 s7) at h3
  obtain ⟨o4,h4,_,b4⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 s4 s5 s6 s7) 4#usize x4 s4 n hn (by decide) rfl rfl hs4
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 s5 s6 s7) at h4
  obtain ⟨o5,h5,_,b5⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 o4 s5 s6 s7) 5#usize x5 s5 n hn (by decide) rfl rfl hs5
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 o5 s6 s7) at h5
  obtain ⟨o6,h6,_,b6⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 o4 o5 s6 s7) 6#usize x6 s6 n hn (by decide) rfl rfl hs6
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 o5 o6 s7) at h6
  obtain ⟨o7,h7,_,b7⟩ := JFs_TX2_FoldLane.source
    (pack x0 x1 x2 x3 x4 x5 x6 x7) (pack o0 o1 o2 o3 o4 o5 o6 s7) 7#usize x7 s7 n hn (by decide) rfl rfl hs7
  change JFs_TX2_FoldLane.lane _ _ _=ok (pack o0 o1 o2 o3 o4 o5 o6 o7) at h7
  refine ⟨o0,o1,o2,o3,o4,o5,o6,o7,?_,⟨b0,b1,b2,b3,b4,b5,b6,b7⟩⟩
  simp only [eight,h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]

theorem source (sums limbs : Array U64 8#usize) (n : Nat) (hn : n<7)
    (hs : Bound limbs n) : ∃ out, eight sums limbs=ok out ∧ Bound out (n+1) := by
  obtain ⟨x0,x1,x2,x3,x4,x5,x6,x7,rfl⟩ := JFs_TX2_ArrayEight.shape sums
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := JFs_TX2_ArrayEight.shape limbs
  simp only [Bound,pack,Array.make,List.mem_cons,List.not_mem_nil,IsEmpty.forall_iff,
    and_true,forall_eq_or_imp,forall_const] at hs
  obtain ⟨o0,o1,o2,o3,o4,o5,o6,o7,run,bounds⟩ := packed x0 x1 x2 x3 x4 x5 x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 n hn hs
  refine ⟨pack o0 o1 o2 o3 o4 o5 o6 o7,run,?_⟩
  simpa only [Bound,pack,Array.make,List.mem_cons,List.not_mem_nil,IsEmpty.forall_iff,
    and_true,forall_eq_or_imp,forall_const] using bounds

#print axioms packed
#print axioms source
end AspisR1.JFs_TX2_FoldEight
end
