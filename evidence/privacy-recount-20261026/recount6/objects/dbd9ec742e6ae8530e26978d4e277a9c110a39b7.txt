import R1Z.PV_AL_CircleOwnedTypes
import R1Z.ProverRwFullTypes
open Aeneas Aeneas.Std
namespace R1Z.PV_AL_CircleCarriers
set_option autoImplicit false
abbrev NCM := ProverRwFull.aspis_core.field.CM31
abbrev RCM := PV_AL_CircleOwned.aspis_core.field.CM31
abbrev NQ := ProverRwFull.aspis_core.field.QM31
abbrev RQ := PV_AL_CircleOwned.aspis_core.field.QM31
abbrev NP := ProverRwFull.aspis_core.circle.SecureCirclePoint
abbrev RP := PV_AL_CircleOwned.aspis_core.circle.SecureCirclePoint
abbrev NR := ProverRwFull.aspis_core.r0_transcript.CircleRow
abbrev RR := PV_AL_CircleOwned.aspis_core.r0_transcript.CircleRow

def encodeCM (x : NCM) : RCM := ⟨x.a,x.b⟩
def decodeCM (x : RCM) : NCM := ⟨x.a,x.b⟩
def encodeQ (x : NQ) : RQ := ⟨encodeCM x.c0,encodeCM x.c1⟩
def decodeQ (x : RQ) : NQ := ⟨decodeCM x.c0,decodeCM x.c1⟩
def encodePoint (x : NP) : RP := ⟨encodeQ x.x,encodeQ x.y⟩
def decodePoint (x : RP) : NP := ⟨decodeQ x.x,decodeQ x.y⟩
def encodeRow : NR → RR | .First => .First | .Second => .Second
def decodeRow : RR → NR | .First => .First | .Second => .Second

theorem native_q (x : NQ) : decodeQ (encodeQ x)=x := rfl
theorem raw_q (x : RQ) : encodeQ (decodeQ x)=x := rfl
theorem native_point (x : NP) : decodePoint (encodePoint x)=x := rfl
theorem raw_point (x : RP) : encodePoint (decodePoint x)=x := rfl
theorem native_row (x : NR) : decodeRow (encodeRow x)=x := by cases x <;> rfl
theorem raw_row (x : RR) : encodeRow (decodeRow x)=x := by cases x <;> rfl

#print axioms encodeCM
#print axioms decodeCM
#print axioms encodeQ
#print axioms decodeQ
#print axioms encodePoint
#print axioms decodePoint
#print axioms encodeRow
#print axioms decodeRow
#print axioms native_q
#print axioms raw_q
#print axioms native_point
#print axioms raw_point
#print axioms native_row
#print axioms raw_row
end R1Z.PV_AL_CircleCarriers
