import RPt_JFr_TX2_DotLaneTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Eight
open Aeneas Aeneas.Std Result
abbrev P := JFr_TX2_DotBounds.P
def pack {α : Type} (a b c d e f g h : α) : Array α 8#usize :=
  Array.make 8#usize [a,b,c,d,e,f,g,h]

theorem source (c0 c1 c2 c3 c4 c5 c6 c7 scalar : U32)
    (s0 s1 s2 s3 s4 s5 s6 s7 : U64) (n : Nat)
    (hc : c0.val<P ∧ c1.val<P ∧ c2.val<P ∧ c3.val<P ∧ c4.val<P ∧ c5.val<P ∧ c6.val<P ∧ c7.val<P)
    (hscalar : scalar.val<P) (hn : n<4)
    (hs : s0.val≤n*((P-1)*(P-1)) ∧ s1.val≤n*((P-1)*(P-1)) ∧ s2.val≤n*((P-1)*(P-1)) ∧ s3.val≤n*((P-1)*(P-1)) ∧ s4.val≤n*((P-1)*(P-1)) ∧ s5.val≤n*((P-1)*(P-1)) ∧ s6.val≤n*((P-1)*(P-1)) ∧ s7.val≤n*((P-1)*(P-1))) :
    ∃ o0 o1 o2 o3 o4 o5 o6 o7 : U64,
      JFr_TX2_DotLanes.eight (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar
        (pack s0 s1 s2 s3 s4 s5 s6 s7)=ok (pack o0 o1 o2 o3 o4 o5 o6 o7) ∧
      (o0.val=s0.val+c0.val*scalar.val ∧ o1.val=s1.val+c1.val*scalar.val ∧ o2.val=s2.val+c2.val*scalar.val ∧ o3.val=s3.val+c3.val*scalar.val ∧ o4.val=s4.val+c4.val*scalar.val ∧ o5.val=s5.val+c5.val*scalar.val ∧ o6.val=s6.val+c6.val*scalar.val ∧ o7.val=s7.val+c7.val*scalar.val) ∧
      (o0.val≤(n+1)*((P-1)*(P-1)) ∧ o1.val≤(n+1)*((P-1)*(P-1)) ∧ o2.val≤(n+1)*((P-1)*(P-1)) ∧ o3.val≤(n+1)*((P-1)*(P-1)) ∧ o4.val≤(n+1)*((P-1)*(P-1)) ∧ o5.val≤(n+1)*((P-1)*(P-1)) ∧ o6.val≤(n+1)*((P-1)*(P-1)) ∧ o7.val≤(n+1)*((P-1)*(P-1))) := by
  rcases hc with ⟨hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7⟩
  rcases hs with ⟨hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7⟩
  obtain ⟨o0,h0,v0,b0⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c0
    (pack s0 s1 s2 s3 s4 s5 s6 s7) 0#usize s0 n (by decide) rfl rfl hc0 hscalar hn hs0
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 s1 s2 s3 s4 s5 s6 s7) at h0
  obtain ⟨o1,h1,v1,b1⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c1
    (pack o0 s1 s2 s3 s4 s5 s6 s7) 1#usize s1 n (by decide) rfl rfl hc1 hscalar hn hs1
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 o1 s2 s3 s4 s5 s6 s7) at h1
  obtain ⟨o2,h2,v2,b2⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c2
    (pack o0 o1 s2 s3 s4 s5 s6 s7) 2#usize s2 n (by decide) rfl rfl hc2 hscalar hn hs2
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 o1 o2 s3 s4 s5 s6 s7) at h2
  obtain ⟨o3,h3,v3,b3⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c3
    (pack o0 o1 o2 s3 s4 s5 s6 s7) 3#usize s3 n (by decide) rfl rfl hc3 hscalar hn hs3
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 o1 o2 o3 s4 s5 s6 s7) at h3
  obtain ⟨o4,h4,v4,b4⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c4
    (pack o0 o1 o2 o3 s4 s5 s6 s7) 4#usize s4 n (by decide) rfl rfl hc4 hscalar hn hs4
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 o1 o2 o3 o4 s5 s6 s7) at h4
  obtain ⟨o5,h5,v5,b5⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c5
    (pack o0 o1 o2 o3 o4 s5 s6 s7) 5#usize s5 n (by decide) rfl rfl hc5 hscalar hn hs5
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 o1 o2 o3 o4 o5 s6 s7) at h5
  obtain ⟨o6,h6,v6,b6⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c6
    (pack o0 o1 o2 o3 o4 o5 s6 s7) 6#usize s6 n (by decide) rfl rfl hc6 hscalar hn hs6
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 o1 o2 o3 o4 o5 o6 s7) at h6
  obtain ⟨o7,h7,v7,b7⟩ := JFr_TX2_DotLaneTotal.source
    (pack c0 c1 c2 c3 c4 c5 c6 c7) scalar c7
    (pack o0 o1 o2 o3 o4 o5 o6 s7) 7#usize s7 n (by decide) rfl rfl hc7 hscalar hn hs7
  change JFr_TX2_DotLanes.lane _ _ _ _=ok (pack o0 o1 o2 o3 o4 o5 o6 o7) at h7
  refine ⟨o0,o1,o2,o3,o4,o5,o6,o7,?_,⟨v0,v1,v2,v3,v4,v5,v6,v7⟩,⟨b0,b1,b2,b3,b4,b5,b6,b7⟩⟩
  simp only [JFr_TX2_DotLanes.eight,h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]

#print axioms source
end AspisR1.JFs_TX2_Eight
end
