import LIB_Carriers
import LIB_ErrorDebug
import NJM_InvocationRoots
import NKA_ClaimsRoot
import NLH_WrapperRoot
import NHU_Mask
set_option autoImplicit false
noncomputable section
namespace LIB_VScalarCarriers
open Aeneas Aeneas.Std
abbrev RawQ := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev NQ := AspisR1.LPi_FieldValues.NQ
abbrev canonQ := AspisR1.LPi_FieldValues.canonQ
abbrev QM31 := {q : NQ // canonQ q}
def toNative (x : RawQ) : NQ :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromNative (x : NQ) : RawQ :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toRaw (x : QM31) : RawQ := fromNative x.val
def CanonicalRaw (x : RawQ) : Prop := canonQ (toNative x)
def ofRaw (x : RawQ) (h : CanonicalRaw x) : QM31 := ⟨toNative x,h⟩
theorem native_roundtrip (x : NQ) : toNative (fromNative x) = x := by cases x; rfl
theorem raw_roundtrip (x : RawQ) : fromNative (toNative x) = x := by cases x; rfl
theorem toRaw_ofRaw (x : RawQ) (h : CanonicalRaw x) : toRaw (ofRaw x h) = x :=
 raw_roundtrip x
theorem toRaw_canonical (x : QM31) : CanonicalRaw (toRaw x) := by
 change canonQ (toNative (fromNative x.val))
 rw [native_roundtrip]
 exact x.property
def array {A B : Type} {n : Usize} (f : A → B) (a : Array A n) : Array B n :=
 ⟨a.val.map f,by simpa using a.property⟩
theorem array_inverse {A B : Type} {n : Usize} (f : A → B) (g : B → A)
 (h : ∀ x,g (f x) = x) (a : Array A n) : array g (array f a) = a := by
 apply Subtype.ext
 change (a.val.map f).map g = a.val
 simp only [List.map_map,Function.comp_def,h,List.map_id]
def qDec : DecidableEq QM31 := Classical.decEq _
#print axioms native_roundtrip
#print axioms raw_roundtrip
#print axioms toRaw_ofRaw
#print axioms toRaw_canonical
#print axioms array_inverse
end LIB_VScalarCarriers
