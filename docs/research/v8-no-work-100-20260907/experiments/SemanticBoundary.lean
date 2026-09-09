import AffinePrimal
namespace AspisV8.SemanticBoundary
open AspisV8.AffinePrimal
theorem sum_range (xs : List Nat) (h : ∀ x∈xs,x≤m) : xs.sum≤xs.length*m := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha:=h a (by simp)
    have hs:=ih (by intro x hx;exact h x (by simp [hx]))
    simp only [List.sum_cons,List.length_cons]
    nlinarith
theorem tail_prefix (n s x : Nat) (hn:n<26) (hs:s≤n*m) (hx:x≤m) :
    (s+x)%word=s+x ∧ s+x≤(n+1)*m := by
  have hpost:s+x≤(n+1)*m := by nlinarith
  have hw:s+x<word := by dsimp [m,p,word] at *;omega
  exact ⟨Nat.mod_eq_of_lt hw,hpost⟩
theorem subtract_ranges (a c s : Nat) (ha:a≤m) (hc:c≤m) (hs:s≤26*m) :
    a+28*p<word ∧ 2*c≤a+28*p ∧ s≤a+28*p-2*c ∧
    (a+28*p-2*c-s)<word := by
  dsimp [m,p,word] at *
  omega
theorem literal_wrapping (a c s : Nat) (ha:a≤m) (hc:c≤m) (hs:s≤26*m) :
    (a+28*p)%word=a+28*p ∧ (2*c)%word=2*c ∧
    (a+28*p+word-2*c)%word=a+28*p-2*c ∧
    (a+28*p-2*c+word-s)%word=a+28*p-2*c-s := by
  obtain ⟨h0,h1,h2,h3⟩:=subtract_ranges a c s ha hc hs
  have h4:a+28*p-2*c<word := by omega
  have e1:a+28*p+word-2*c=(a+28*p-2*c)+word := by omega
  have e2:a+28*p-2*c+word-s=(a+28*p-2*c-s)+word := by omega
  rw [Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt (show 2*c<word by omega),e1,e2,
    Nat.add_mod_right,Nat.add_mod_right,Nat.mod_eq_of_lt h4,Nat.mod_eq_of_lt h3]
  exact ⟨rfl,rfl,rfl,rfl⟩
theorem reduced_result (a c s : Nat) (ha:a≤m) (hc:c≤m) (hs:s≤26*m) :
    ((a+28*p-2*c-s : Nat):ZMod p)=(a:ZMod p)-2*(c:ZMod p)-(s:ZMod p) := by
  obtain ⟨_,h1,h2,_⟩:=subtract_ranges a c s ha hc hs
  rw [Nat.cast_sub h2,Nat.cast_sub h1]
  simp
theorem actual_boundary (a c s : Nat) (ha:a≤m) (hc:c≤m) (hs:s≤26*m) :
    2*(c:ZMod p)+((a+28*p-2*c-s : Nat):ZMod p)+(s:ZMod p)=(a:ZMod p) := by
  rw [reduced_result a c s ha hc hs]
  ring
theorem list_cast (xs : List Nat) :
    (xs.sum:ZMod p)=(xs.map (fun (x:Nat) => (x:ZMod p))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.sum_cons,List.map_cons,Nat.cast_add,ih]
theorem missing_from_terms (a c : Nat) (xs : List Nat) (ha:a≤m) (hc:c≤m)
    (hlen:xs.length=26) (h : ∀ x∈xs,x≤m) :
    ((a+28*p-2*c-xs.sum : Nat):ZMod p)=
      (a:ZMod p)-2*(c:ZMod p)-(xs.map (fun (x:Nat) => (x:ZMod p))).sum := by
  have hs:xs.sum≤26*m := by simpa [hlen] using sum_range xs h
  rw [reduced_result a c xs.sum ha hc hs,list_cast]
#print axioms sum_range
#print axioms tail_prefix
#print axioms subtract_ranges
#print axioms literal_wrapping
#print axioms reduced_result
#print axioms actual_boundary
#print axioms list_cast
#print axioms missing_from_terms
end AspisV8.SemanticBoundary
