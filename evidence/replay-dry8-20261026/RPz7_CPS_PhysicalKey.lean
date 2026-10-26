import RPz7_CPS_BoundaryLoad
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_PhysicalKey
open Hist_Store Hist_RuntimeEntry CPP_BankState S2W_D189Entry

/-- Account public key, distinct from the invocation-local Nat cell label. -/
def key (e : Entry) (slot : Nat) : Hist_Authority.Key :=
  (e.records (e.handles slot).1).owned.key

theorem loaded (bank : Bank) (layout : Layout) (slot : Nat) :
    key (load bank.cells (CPP_BankState.layout bank layout)) slot =
      (layout.records (layout.handles slot).1).owned.key := rfl

theorem boundary (bank : Bank) (layout : Layout) (slot : Nat) :
    key (CPS_BoundaryLoad.entry bank layout) slot =
      (layout.records (layout.handles slot).1).owned.key := rfl

/-- The precise missing global-map interface: a common injective physical map
and its two source views turn equal public keys into equal BANK cell labels.
This is a conditional map lemma, not an instance from runtime admission. -/
theorem pairing (e1 e2 : Entry) (map : Nat → Hist_Authority.Key)
    (injective : Function.Injective map)
    (writer : key e1 2 = map (e1.handles 2).1)
    (reader : key e2 6 = map (e2.handles 6).1)
    (same : key e1 2 = key e2 6) : (e1.handles 2).1 = (e2.handles 6).1 :=
  injective (writer.symm.trans (same.trans reader))

/-- Equal local labels across independent maps do not identify public keys. -/
theorem independent_maps (left right : Nat → Hist_Authority.Key) (cell : Nat)
    (different : left cell ≠ right cell) :
    ¬ (∀ i j, i = j → left i = right j) := by
  intro global
  exact different (global cell cell rfl)

#print axioms loaded
#print axioms boundary
#print axioms pairing
#print axioms independent_maps
end AspisR1.CPS_PhysicalKey
end
