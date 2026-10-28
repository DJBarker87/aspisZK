import PV_L2C_ListOrigins
import PV_L2C_AccountLayout
set_option autoImplicit false
namespace PV_L2C_AccountOrigins
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_DigestList

/-- Successful ordered account field cut, with the exact returned raw root
and frontier. Native lane/tree association is a separate structural receipt. -/
structure Tree (root : Digest) (frontier : Array Digest 20#usize) where
  bytes : List Bytes
  decoded : List Digest
  count : bytes.length = 21
  success : run bytes = ok (.Ok decoded)
  root_field : decoded[0]? = some root
  frontier_fields : ∀ j : Fin 20, decoded[j.val+1]? = some frontier.val[j.val]!

theorem lookup (bytes : List Bytes) (ds : List Digest) (h : run bytes = ok (.Ok ds))
    (j : Nat) (d : Digest) (he : ds[j]? = some d) : PV_L2C_DigestOrigin.Origin d := by
  have hj : j < ds.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at he
    cases he
  have he' : ds[j] = d := by
    rw [List.getElem?_eq_getElem hj] at he
    exact Option.some.inj he
  rw [← he']
  exact PV_L2C_ListOrigins.field bytes ds h j hj
#print axioms lookup

theorem root (r : Digest) (f : Array Digest 20#usize) (h : Tree r f) :
    PV_L2C_DigestOrigin.Origin r := lookup h.bytes h.decoded h.success 0 r h.root_field
#print axioms root

theorem frontier (r : Digest) (f : Array Digest 20#usize) (h : Tree r f) (j : Fin 20) :
    PV_L2C_DigestOrigin.Origin f.val[j.val]! :=
  lookup h.bytes h.decoded h.success (j.val+1) _ (h.frontier_fields j)
#print axioms frontier
end PV_L2C_AccountOrigins
