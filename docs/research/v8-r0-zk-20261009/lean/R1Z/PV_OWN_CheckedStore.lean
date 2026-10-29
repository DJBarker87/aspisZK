import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_CheckedStore
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations
/-- Permission/range evidence is mandatory at the checked interface boundary.
The raw byte transformer is not itself a permission check for native Rust. -/
structure Command {T : Type} (k : Codec T) (m : Memory) where
 token : Token
 cell : Cell
 owner : Nat
 offset : Nat
 value : T
 writable : Writable m owner token cell
 fits : Fits cell offset k.width

def execute {T : Type} {k : Codec T} {m : Memory} (c : Command k m) : Memory :=
 writeTyped k c.token c.cell c.offset c.value m

theorem representation {T : Type} {k : Codec T} {m : Memory} (c : Command k m) :
 View k (execute c) c.token c.offset c.value := by
 refine ⟨store c.cell c.offset k.width (k.encode c.value),?_,?_⟩
 · exact ⟨put_same _ _ _,c.writable.1.1.2.1,c.writable.1.1.2.2⟩
 · exact initialized k c.cell c.offset c.value c.fits

theorem frame {T : Type} {k : Codec T} {m : Memory} (c : Command k m)
 (a : Nat) (h:a≠c.token.address) : (execute c).heap a=m.heap a := put_other _ _ _ _ h
#print axioms representation
#print axioms frame
end R1Z.PV_OWN_CheckedStore
