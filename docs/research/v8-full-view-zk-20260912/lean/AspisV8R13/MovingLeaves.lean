import AspisV8R13.SwapCells

/-!
A complete moving-address oracle coupling, with BOTH inverse identities.

Index labels disjoint input fibres (in the source: distinct hidden salts and
fixed tree tags). `move` may see the selected complete answers, not the other
answers this construction transposes. That restriction is present in its type.
No freshness, random-oracle probability, or compiler acceptance is assumed.
-/
set_option autoImplicit false
namespace AspisV8R13
variable {C D Index Key Digest : Type*} [DecidableEq Key]

abbrev LeafOracle (Index Key Digest : Type*) := Index → Key → Digest

def selected (H : LeafOracle Index Key Digest) (p : Index → Key) : Index → Digest :=
  fun i => H i (p i)

def swapFamilies (H : LeafOracle Index Key Digest) (old new : Index → Key) :
    LeafOracle Index Key Digest := fun i => swapCells (H i) (old i) (new i)

@[simp] theorem selected_swapFamilies
    (H : LeafOracle Index Key Digest) (old new : Index → Key) :
    selected (swapFamilies H old new) new = selected H old := by
  funext i
  exact swapCells_right (H i) (old i) (new i)

@[simp] theorem swapFamilies_reverse
    (H : LeafOracle Index Key Digest) (old new : Index → Key) :
    swapFamilies (swapFamilies H old new) new old = H := by
  funext i
  exact swapCells_reverse (H i) (old i) (new i)

/-- Source and target payload functions may differ. -/
def oracleMove (left : C → Index → Key) (right : D → Index → Key)
    (move : (Index → Digest) → C ≃ D)
    (world : C × LeafOracle Index Key Digest) : D × LeafOracle Index Key Digest :=
  let handles := selected world.2 (left world.1)
  let y := move handles world.1
  (y, swapFamilies world.2 (left world.1) (right y))

/-- This is the key invariant: the inverse observes precisely the same full
leaf answers and hence selects the inverse of precisely the same coin map. -/
theorem oracleMove_handles (left : C → Index → Key) (right : D → Index → Key)
    (move : (Index → Digest) → C ≃ D)
    (world : C × LeafOracle Index Key Digest) :
    selected (oracleMove left right move world).2
      (right (oracleMove left right move world).1) = selected world.2 (left world.1) := by
  simp only [oracleMove, selected_swapFamilies]

theorem oracleMove_inverse (left : C → Index → Key) (right : D → Index → Key)
    (move : (Index → Digest) → C ≃ D)
    (world : C × LeafOracle Index Key Digest) :
    oracleMove right left (fun h => (move h).symm)
      (oracleMove left right move world) = world := by
  rcases world with ⟨x,H⟩
  simp only [oracleMove, selected_swapFamilies, Equiv.symm_apply_apply,
    swapFamilies_reverse]

/-- A global bijection, not a coupling postulated to have correct marginals. -/
def movingLeafEquiv (left : C → Index → Key) (right : D → Index → Key)
    (move : (Index → Digest) → C ≃ D) :
    (C × LeafOracle Index Key Digest) ≃ (D × LeafOracle Index Key Digest) where
  toFun := oracleMove left right move
  invFun := oracleMove right left (fun h => (move h).symm)
  left_inv := oracleMove_inverse left right move
  right_inv := by
    intro world
    simpa only [Equiv.symm_symm] using
      oracleMove_inverse right left (fun h => (move h).symm) world

#print axioms oracleMove_handles
#print axioms oracleMove_inverse
#print axioms movingLeafEquiv
end AspisV8R13
