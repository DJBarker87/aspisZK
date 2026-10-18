import R0P.Poseidon

/-! Symbolic distribution of the existing R0P external layer through the
literal four-lane pack. Matrix evaluation stays opaque. This is the model
boundary for the actual packed implementation's per-group map and total sum. -/
set_option autoImplicit false
namespace AspisR1.PoseidonExternalPackedModel
variable {K : Type} [Field K]

def lane (group column : Fin 4) : Fin 16 :=
  ⟨4 * group.val + column.val,by have := group.isLt; have := column.isLt; omega⟩

def localCell (state : Fin 16 → K) (group column : Fin 4) : K :=
  R0P.poseidonMat4 (fun j => state (lane group j)) column

def localPacked (state : Fin 16 → K) (i u : K) (group : Fin 4) : K :=
  R0P.poseidonPackingFormula i u (localCell state group)

theorem external_cell (state : Fin 16 → K) (group column : Fin 4) :
    R0P.poseidonExternalLinear state (lane group column) =
      localCell state group column +
        ((((0 + localCell state 0 column) + localCell state 1 column) +
          localCell state 2 column) + localCell state 3 column) := by
  let gi : Fin 4 := ⟨(4 * group.val + column.val) / 4,by
    have := group.isLt; have := column.isLt; omega⟩
  let ci : Fin 4 := ⟨(4 * group.val + column.val) % 4,Nat.mod_lt _ (by decide)⟩
  have hg : gi = group := by
    apply Fin.ext
    change (4 * group.val + column.val) / 4 = group.val
    have := column.isLt
    omega
  have hc : ci = column := by
    apply Fin.ext
    change (4 * group.val + column.val) % 4 = column.val
    have := column.isLt
    omega
  change localCell state gi ci +
      ((((0 + localCell state 0 ci) + localCell state 1 ci) +
        localCell state 2 ci) + localCell state 3 ci) = _
  rw [hg,hc]

theorem packed_external_eq (state : Fin 16 → K) (i u : K) (group : Fin 4) :
    R0P.poseidonPackingFormula i u
        (fun j => R0P.poseidonExternalLinear state (lane group j)) =
      localPacked state i u group +
        ((((0 + localPacked state i u 0) + localPacked state i u 1) +
          localPacked state i u 2) + localPacked state i u 3) := by
  simp only [localPacked,R0P.poseidonPackingFormula,external_cell]
  ring

theorem packed_external_eq_pack4 {F : Subfield K} (B : R0P.PackBasis F)
    (state : Fin 16 → K) (group : Fin 4) :
    R0P.pack4 B (fun j => R0P.poseidonExternalLinear state (lane group j)) =
      localPacked state B.i B.u group +
        ((((0 + localPacked state B.i B.u 0) + localPacked state B.i B.u 1) +
          localPacked state B.i B.u 2) + localPacked state B.i B.u 3) := by
  simpa only [R0P.pack4,R0P.poseidonPackingFormula] using
    packed_external_eq state B.i B.u group

#print axioms external_cell
#print axioms packed_external_eq
#print axioms packed_external_eq_pack4
end AspisR1.PoseidonExternalPackedModel
