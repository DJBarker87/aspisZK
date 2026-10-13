import AspisFormal.Pool.IncrementalMerkleV1

/-! The concrete first-zero/full carry cases reconstruct the chronological
post-append tree from the same open-capacity frontier invariant. -/
set_option autoImplicit false

namespace AspisPool.IncrementalMerkleV1

theorem append_reconstruct_afterstate {α : Type}
    (parent : α → α → α) (emptyLeaf leaf : α) (depth : Nat)
    (leaves : List α) (frontier : List (Option α))
    (inv : FrontierInvariant parent emptyLeaf depth leaves frontier) :
    reconstructFrom parent emptyLeaf 0 leaf frontier =
      rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]) := by
  cases h : appendCarry parent leaf frontier with
  | more updated =>
      have hcarry := appendCarry_reconstruct_more parent emptyLeaf leaf 0
        frontier updated h
      have happend := append_correct parent emptyLeaf leaf depth leaves
        frontier updated inv h
      have hroot := happend.2
      change reconstructFrom parent emptyLeaf 0 emptyLeaf updated =
        rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]) at hroot
      calc
        reconstructFrom parent emptyLeaf 0 leaf frontier =
            reconstructFrom parent emptyLeaf 0 emptyLeaf updated := hcarry.symm
        _ = rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]) := hroot
  | full root =>
      have hcarry := appendCarry_reconstruct_full parent emptyLeaf leaf root 0
        frontier h
      have hterminal := append_terminal_correct parent emptyLeaf leaf root depth
        leaves frontier inv h
      calc
        reconstructFrom parent emptyLeaf 0 leaf frontier = root := hcarry.symm
        _ = rootWithEmptySuffix parent emptyLeaf depth (leaves ++ [leaf]) :=
          hterminal.2

#print axioms append_reconstruct_afterstate

end AspisPool.IncrementalMerkleV1
