import NBO_Audit
set_option autoImplicit false
namespace NBW_DotWindows
/-- Six four-product groups followed by the remaining two products for the
frozen 26-term base prefix. The element type is independent of arithmetic. -/
def windows {α : Type} : Nat → List α → List (List α)
 | 0, xs => [xs]
 | n+1, xs => xs.take 4 :: windows n (xs.drop 4)
theorem flatten {α : Type} (n : Nat) (xs : List α) :
 (windows n xs).flatten=xs := by
 induction n generalizing xs with
 | zero => simp [windows]
 | succ n ih => simp [windows,ih]
theorem count {α : Type} (n : Nat) (xs : List α) :
 (windows n xs).length=n+1 := by
 induction n generalizing xs with
 | zero => rfl
 | succ n ih => simp [windows,ih]
theorem extent {α : Type} (n : Nat) (xs : List α) (bound : xs.length≤4*(n+1)) :
 ∀ block ∈ windows n xs, block.length≤4 := by
 induction n generalizing xs with
 | zero =>
   intro block mem
   have same : block=xs := by simpa [windows] using mem
   subst block;omega
 | succ n ih =>
   intro block mem
   have split : block=xs.take 4 ∨ block∈windows n (xs.drop 4) := by
     simpa only [windows,List.mem_cons] using mem
   rcases split with same | rest
   · subst block
     simp only [List.length_take];omega
   · apply ih (xs.drop 4) (by simp only [List.length_drop];omega) block rest
/-- Every arithmetic-domain bound on original products transfers to the
actual grouped product, without selecting an independent product list. -/
theorem member {α : Type} (n : Nat) (xs block : List α) (x : α)
 (group : block∈windows n xs) (element : x∈block) : x∈xs := by
 have h : x∈(windows n xs).flatten := List.mem_flatten.mpr ⟨block,group,element⟩
 simpa only [flatten] using h
/-- Frozen schedule inventory; native source iteration association is still
required. No four_dots Result equality or digest behavior is assumed. -/
theorem frozen26 {α : Type} (xs : List α) (size : xs.length=26) :
 (windows 6 xs).length=7 ∧ (windows 6 xs).flatten=xs ∧
 (∀ block∈windows 6 xs, block.length≤4) ∧ (xs.drop 24).length=2 := by
 refine ⟨count 6 xs,flatten 6 xs,extent 6 xs (by omega),?_⟩
 simp only [List.length_drop,size]
#print axioms flatten
#print axioms count
#print axioms extent
#print axioms member
#print axioms frozen26
end NBW_DotWindows
