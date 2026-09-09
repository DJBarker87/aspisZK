import QueryInjection
namespace AspisV8.TerminalQuery
open scoped BigOperators
variable {R : Type*} [CommRing R]
def pi (x:R) : R := 2*x*x-1
-- Literal low-bit traversal used by LineM31Batch.weight_at.
def indexed : Nat → Nat → R → R → R
  | 0,_,s,_ => s
  | n+1,i,s,x => indexed n (i/2) (if i%2=0 then s else s*x) (pi x)
def shared (s x:R) : Fin 4 → R := ![s,s*x,s*pi x,(s*x)*pi x]
-- The public weight_prefix path takes index3 from index2, whereas the
-- proposed fixed path reuses index1. Commutativity justifies that difference.
def prefix4 (s x:R) : Fin 4 → R := ![s,s*x,s*pi x,(s*pi x)*x]
theorem shared_indexed (s x:R) (i:Fin 4) : shared s x i=indexed 2 i.val s x := by
  fin_cases i <;> simp [shared,indexed]
theorem prefix_shared (s x:R) : prefix4 s x=shared s x := by
  funext i;fin_cases i <;> simp [prefix4,shared] <;> ring
def vectorSum (xs:List (R×R)) : Fin 4 → R :=
  xs.foldl (fun t sx => t+shared sx.1 sx.2) 0
theorem apply_fold (xs:List (R×R)) (s:Fin 4→R) (i:Fin 4) :
    xs.foldl (fun t sx => t+shared sx.1 sx.2) s i =
      xs.foldl (fun t sx => t+indexed 2 i.val sx.1 sx.2) (s i) := by
  induction xs generalizing s with
  | nil => rfl
  | cons sx xs ih => simp only [List.foldl_cons,ih,Pi.add_apply,shared_indexed]
theorem vectorSum_indexed (xs:List (R×R)) (i:Fin 4) :
    vectorSum xs i=xs.foldl (fun t sx => t+indexed 2 i.val sx.1 sx.2) 0 := by
  exact apply_fold xs 0 i
def halves (h:R) : Nat → R → R
  | 0,x => x
  | n+1,x => halves h n (x*h)
theorem halves_power (h x:R) (n:Nat) : halves h n x=x*h^n := by
  induction n generalizing x with
  | zero => simp [halves]
  | succ n ih => simp only [halves,ih,pow_succ];ring
theorem halves_add (h x y:R) (n:Nat) :
    halves h n (x+y)=halves h n x+halves h n y := by
  simp only [halves_power];ring
def terminal (h:R) (xs:List (R×R)) : Fin 4→R := fun i=>halves h 6 (vectorSum xs i)
theorem halved_vector_indexed (h:R) (n:Nat) (xs:List (R×R)) (i:Fin 4) :
    halves h n (vectorSum xs i)=halves h n (xs.foldl (fun t sx=>t+indexed 2 i.val sx.1 sx.2) 0) := by
  rw [vectorSum_indexed]
theorem terminal_indexed (h:R) (xs:List (R×R)) (i:Fin 4) :
    terminal h xs i=halves h 6 (xs.foldl (fun t sx=>t+indexed 2 i.val sx.1 sx.2) 0) := by
  simp only [terminal,vectorSum_indexed]
-- The batch's exact dual factor. Its normalization is still carried; it is
-- not silently discarded because the final values happen to vanish.
def factor (a x:R) : R := 1+a^3*x+a^2*pi x+a*(pi x*x)
def dual (a:R) (v:Fin 4→R) : R := v 0+a^3*v 1+a^2*v 2+a*v 3
theorem factor_is_dual (s a x:R) : s*factor a x=dual a (shared s x) := by
  simp [factor,dual,shared];ring
theorem defer_two_halves (h s a x:R) (n:Nat) :
    halves h (n+2) (s*factor a x)=
      halves h n (s*(factor a x*h*h)) := by
  simp only [halves_power,pow_add,pow_two];ring
-- Sparse image contribution is merged into coefficient3, never omitted.
def oldTerminal (o q f:Fin 4→R) (im:R) : R :=
  (∑ i,(o i+q i)*f i)+im*f 3
def fusedTerminal (o q f:Fin 4→R) (im:R) : R :=
  ∑ i,(o i+q i+(if i=3 then im else 0))*f i
theorem image_fusion (o q f:Fin 4→R) (im:R) :
    fusedTerminal o q f im=oldTerminal o q f im := by
  simp [fusedTerminal,oldTerminal,Fin.sum_univ_succ];ring
theorem terminal_check_equivalence (o q f:Fin 4→R) (im claim:R) :
    (fusedTerminal o q f im=claim) ↔ (oldTerminal o q f im=claim) := by
  rw [image_fusion]
open AspisV8.AffinePrimal AspisV8.SemanticCarry AspisV8.SharedGammaDots
-- Literal four-product helper used by the fused terminal: canonical nine-
-- channel decomposition, fresh raw group, one partial reconstruction.
theorem partial_raw_result (xs:List (Q Nat × Q Nat)) :
    reconstruct (castC (partialC (rawGroup xs)))=
      xs.foldl (fun t xy=>t+towerMul (castQ xy.1) (castQ xy.2)) 0 := by
  have h:castC (partialC (rawGroup xs))=castC (rawGroup xs) := by
    funext i j;simp only [castC,partialC,partial_cast]
  rw [h];exact AspisV8.QueryAffine.helper_result xs
theorem four_product_range (n s a b:Nat) (hn:n<4) (hs:s≤n*m^2) (ha:a≤m) (hb:b≤m) :
    s+a*b≤(n+1)*m^2 ∧ (s+(a*b)%word)%word=s+a*b :=
  four_product_prefix n s a b hn hs ha hb
theorem selected_dimensions : 8-2-2-2=2 ∧ 2+2+2=6 ∧ 2^2=4 := by norm_num
#print axioms shared_indexed
#print axioms prefix_shared
#print axioms apply_fold
#print axioms vectorSum_indexed
#print axioms halves_power
#print axioms halves_add
#print axioms terminal_indexed
#print axioms halved_vector_indexed
#print axioms factor_is_dual
#print axioms defer_two_halves
#print axioms image_fusion
#print axioms terminal_check_equivalence
#print axioms partial_raw_result
#print axioms four_product_range
#print axioms selected_dimensions
end AspisV8.TerminalQuery
