import R1Z.PV_OWN_Bytes
set_option autoImplicit false
namespace R1Z.PV_OWN_View
open PV_OWN_Heap PV_OWN_Bytes
structure Codec (T : Type) where
  width : Nat
  alignment : Nat
  positive_alignment : alignment>0
  encode : T → Bytes
  injective : ∀ a b, (∀ i, i<width → encode a i=encode b i) → a=b
/-- Representation includes padding as None, never invents initialized bytes. -/
def Represents {T : Type} (codec : Codec T) (c : Cell) (start : Nat) (value : T) : Prop :=
  Fits c start codec.width ∧ ∀ i, i<codec.width → c.contents (start+i)=codec.encode value i

def View {T : Type} (codec : Codec T) (m : Memory) (t : Token) (start : Nat) (v : T) : Prop :=
  ∃ c, Live m t c ∧ Represents codec c start v

theorem initialized {T : Type} (codec : Codec T) (c : Cell) (s : Nat) (v : T)
    (fits : Fits c s codec.width) : Represents codec (store c s codec.width (codec.encode v)) s v :=
  ⟨fits,fun i hi => inside _ _ _ _ _ hi⟩
theorem unique {T : Type} (codec : Codec T) (c : Cell) (s : Nat) (a b : T)
    (ha:Represents codec c s a) (hb:Represents codec c s b) : a=b := by
  apply codec.injective
  intro i hi
  exact (ha.2 i hi).symm.trans (hb.2 i hi)
theorem read_initialized {T : Type} (codec : Codec T) (c : Cell) (s i : Nat) (v : T)
    (h:Represents codec c s v) (hi:i<codec.width) :
    c.contents (s+i)=codec.encode v i := h.2 i hi
#print axioms initialized
#print axioms unique
#print axioms read_initialized
end R1Z.PV_OWN_View
