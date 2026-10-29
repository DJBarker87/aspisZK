import R1Z.PV_OWN_Bytes
set_option autoImplicit false
namespace R1Z.PV_OWNB_Padding
open PV_OWN_Bytes
/-- Only initialized representation bytes constrain native storage. -/
def Agrees (required actual : Bytes) : Prop :=
 ∀ i b, required i=some b → actual i=some b

def normalize (required actual : Bytes) : Bytes :=
 fun i => match required i with | none => none | some _ => actual i

theorem refl (a : Bytes) : Agrees a a := fun _ _ h => h

theorem trans (a b c : Bytes) (hab:Agrees a b) (hbc:Agrees b c) : Agrees a c :=
 fun i v h => hbc i v (hab i v h)

theorem normalization (a b : Bytes) (h:Agrees a b) : normalize a b=a := by
 funext i
 cases hi:a i with
 | none => simp [normalize,hi]
 | some v => simp [normalize,hi,h i v hi]

theorem of_normalization (a b : Bytes) (h:normalize a b=a) : Agrees a b := by
 intro i v hi
 have hh:=congrFun h i
 simpa [normalize,hi] using hh

attribute [local irreducible] Agrees normalize
#print axioms refl
#print axioms trans
#print axioms normalization
#print axioms of_normalization
end R1Z.PV_OWNB_Padding
