import R1SpendDataMap
import R0P.CoreExt

/-! A structural typing fact: mapping a public statement through a ring
homomorphism places every field-valued coordinate in that homomorphism's
range. -/
set_option autoImplicit false

namespace AspisR1.PublicBaseMap

open R0P

variable {K L : Type} [Field K] [Field L]

theorem mapPublic_base (f : K →+* L) (pub : Public K) :
    PublicBase f.fieldRange (AspisR1.SpendDataMap.mapPublic f pub) := by
  unfold PublicBase AspisR1.SpendDataMap.mapPublic
  constructor
  · intro i
    exact f.mem_fieldRange_self _
  constructor
  · intro i
    exact f.mem_fieldRange_self _
  constructor
  · exact f.mem_fieldRange_self _
  constructor
  · intro r hr i
    cases hrecipient : pub.recipient with
    | none => simp [hrecipient] at hr
    | some d =>
        simp only [hrecipient, Option.map_some] at hr
        subst r
        exact f.mem_fieldRange_self _
  constructor
  · intro i
    exact f.mem_fieldRange_self _
  constructor
  · intro a ha
    cases hamount : pub.withdrawalAmount with
    | none => simp [hamount] at ha
    | some x =>
        simp only [hamount, Option.map_some] at ha
        subst a
        exact f.mem_fieldRange_self _
  constructor
  · intro l i
    exact f.mem_fieldRange_self _
  constructor
  · intro i
    exact f.mem_fieldRange_self _
  · intro l i
    exact f.mem_fieldRange_self _

#print axioms mapPublic_base

end AspisR1.PublicBaseMap
