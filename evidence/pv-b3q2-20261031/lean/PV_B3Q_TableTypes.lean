import PV_B3Q_PanicGuards
namespace PV_B3Q_FrozenTables
set_option autoImplicit false
abbrev Endpoint := Nat × Nat × Nat
abbrev Link := Nat × Nat × Endpoint × Endpoint
def endpointSafe (e : Endpoint) : Bool := decide (e.1 < 1024 ∧ e.2.1 < 2 ∧ e.2.2 < 14)
def linkSafe (l : Link) : Bool := decide (l.1 < 5 ∧ l.2.1 < 64) && endpointSafe l.2.2.1 && endpointSafe l.2.2.2
def maskSafe (m : Nat) : Bool := decide (m = 6144 ∨ m = 6145 ∨ m = 4097 ∨ m = 2048 ∨ m = 2049 ∨ m = 26214 ∨ m = 1749)
end PV_B3Q_FrozenTables
