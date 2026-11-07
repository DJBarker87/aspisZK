import LIB_VScalarCarriers
import NNG_Transport_T1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBScalar
open Aeneas Aeneas.Std NNG_Transport
abbrev Raw := NNG_verify_finish.aspis_core.field.QM31
abbrev Value := LIB_VScalarCarriers.QM31
def Domain (x : Raw) : Prop := LIB_VScalarCarriers.CanonicalRaw (toT1 x)
def lower (x : Value) : Raw := fromT1 (LIB_VScalarCarriers.toRaw x)
/-- Total projection uses an input canonical scalar only outside Domain;
all source equality uses prove Domain from CLOSED returned-value laws. -/
def project (fallback : Value) (x : Raw) : Value :=
  if h : Domain x then LIB_VScalarCarriers.ofRaw (toT1 x) h else fallback

theorem lower_domain (x : Value) : Domain (lower x) := by
  unfold Domain lower
  rw [fromT1_inverse]
  exact LIB_VScalarCarriers.toRaw_canonical x
#print axioms lower_domain

theorem lower_project (fallback : Value) (x : Raw) (h : Domain x) :
    lower (project fallback x) = x := by
  unfold project
  rw [dif_pos h]
  unfold lower
  rw [LIB_VScalarCarriers.toRaw_ofRaw,toT1_inverse]
#print axioms lower_project

theorem project_lower (fallback x : Value) : project fallback (lower x) = x := by
  unfold project
  rw [dif_pos (lower_domain x)]
  apply Subtype.ext
  change LIB_VScalarCarriers.toNative (toT1 (fromT1 (LIB_VScalarCarriers.fromNative x.val))) = x.val
  rw [fromT1_inverse,LIB_VScalarCarriers.native_roundtrip]
#print axioms project_lower

theorem injective_on (fallback : Value) (x y : Raw) (hx : Domain x) (hy : Domain y)
    (same : project fallback x = project fallback y) : x = y := by
  have h := congrArg lower same
  rw [lower_project fallback x hx,lower_project fallback y hy] at h
  exact h
#print axioms injective_on
end AspisR1.NNG_LIBScalar
