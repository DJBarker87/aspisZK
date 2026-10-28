import PV_L2D_MerkleGeometry
set_option autoImplicit false
namespace PV_L2D_MerkleSafe
open PV_L2D_MerklePlan PV_L2D_MerkleGeometry PV_L2D_MerkleOrdered

theorem sibling_mem (fuel : Nat) (xs : List Nat) (p : Nat)
    (h : p ∈ (level fuel xs).2) : ∃ x ∈ xs, p=sibling x := by
  induction fuel generalizing xs with
  | zero => simp [level] at h
  | succ n ih =>
    cases xs with
    | nil => simp [level] at h
    | cons x xs =>
      simp only [level] at h
      split at h
      · obtain ⟨y,hy,he⟩ := ih xs.tail h
        exact ⟨y,List.mem_cons_of_mem x (tail_mem hy),he⟩
      · simp only [List.mem_cons] at h
        rcases h with he | ht
        · exact ⟨x,by simp,he⟩
        · obtain ⟨y,hy,he⟩ := ih xs ht
          exact ⟨y,List.mem_cons_of_mem x hy,he⟩
#print axioms sibling_mem

theorem addresses_safe (n depth : Nat) (xs : List Nat)
    (bound : ∀ x ∈ xs, x<2^n) :
    ∀ a∈plan n depth xs,
      depth≤a.1 ∧ a.1<depth+n ∧ a.2<2^(n-(a.1-depth)) := by
  induction n generalizing depth xs with
  | zero => simp [plan]
  | succ n ih =>
    intro a ha
    simp only [plan,List.mem_append,List.mem_map] at ha
    rcases ha with hfirst | hrest
    · obtain ⟨p,hp,rfl⟩ := hfirst
      obtain ⟨x,hx,rfl⟩ := sibling_mem xs.length xs p hp
      have hb:=bound x hx
      have hs:=sibling_bound x (2^n) (by simpa [pow_succ,Nat.mul_comm] using hb)
      simp only [Nat.sub_self,Nat.sub_zero]
      refine ⟨le_refl _,by omega,?_⟩
      simpa [pow_succ,Nat.mul_comm] using hs
    · have hb : ∀ p∈(level xs.length xs).1,p<2^n := by
        simpa using level_bound xs.length xs (n+1) bound
      obtain ⟨hlo,hhi,hval⟩ := ih (depth+1) (level xs.length xs).1 hb a hrest
      have he : n+1-(a.1-depth)=n-(a.1-(depth+1)) := by omega
      exact ⟨by omega,by omega,by simpa only [he] using hval⟩
#print axioms addresses_safe

/-- The callback's complete depth/index pair is valid in an 18-bit tree;
this is stronger than a bound only on the number of returned siblings. -/
theorem eighteen (xs : List Nat) (domain : ∀ x∈xs,x<2^18) :
    ∀ a∈plan 18 0 xs,a.1<18 ∧ a.2<2^(18-a.1) := by
  intro a ha
  obtain ⟨_,hd,hi⟩:=addresses_safe 18 0 xs domain a ha
  exact ⟨by simpa using hd,by simpa using hi⟩
#print axioms eighteen
end PV_L2D_MerkleSafe
