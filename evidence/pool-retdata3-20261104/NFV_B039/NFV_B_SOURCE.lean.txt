import NFV_RequestOracle
set_option autoImplicit false
namespace NFV_RequestIndexes
open Aeneas Aeneas.Std NFV_Envelope

theorem window {T : Type} (before part after : List T) (start i : Nat)
    (position : before.length = start) (inside : start ≤ i) (bound : i-start < part.length) :
    (before ++ part ++ after)[i]? = part[i-start]? := by
  rw [List.append_assoc,List.getElem?_append_right (by omega)]
  rw [position,List.getElem?_append_left bound]
#print axioms window

theorem header (profile release program : Bytes32) (kind : U8) (payment : Payment)
    (j : Nat) (bounded : j < 8) :
    (pure profile release program kind payment).val[j]? = (headerBytes kind)[j]? := by
  rw [pure_value]
  simpa only [List.nil_append,List.append_assoc,Nat.sub_zero] using
    window [] (headerBytes kind) (profile.val ++ release.val ++ program.val ++ payment.val) 0 j rfl
      (Nat.zero_le j) (by simpa [headerBytes] using bounded)
#print axioms header

theorem profile (profile release program : Bytes32) (kind : U8) (payment : Payment)
    (j : Nat) (lower : 8 ≤ j) (upper : j < 40) :
    (pure profile release program kind payment).val[j]? = profile.val[j-8]? := by
  have hp : profile.val.length = 32 := profile.property
  rw [pure_value]
  simpa only [List.append_assoc] using
    window (headerBytes kind) profile.val (release.val ++ program.val ++ payment.val) 8 j
      (by simp [headerBytes]) lower (by omega)
#print axioms profile

theorem release (profile release program : Bytes32) (kind : U8) (payment : Payment)
    (j : Nat) (lower : 40 ≤ j) (upper : j < 72) :
    (pure profile release program kind payment).val[j]? = release.val[j-40]? := by
  have hp : profile.val.length = 32 := profile.property
  have hr : release.val.length = 32 := release.property
  rw [pure_value]
  simpa only [List.append_assoc] using
    window (headerBytes kind ++ profile.val) release.val (program.val ++ payment.val) 40 j
      (by simp [headerBytes,hp]) lower (by omega)
#print axioms release

theorem program (profile release program : Bytes32) (kind : U8) (payment : Payment)
    (j : Nat) (lower : 72 ≤ j) (upper : j < 104) :
    (pure profile release program kind payment).val[j]? = program.val[j-72]? := by
  have hp : profile.val.length = 32 := profile.property
  have hr : release.val.length = 32 := release.property
  have hb : program.val.length = 32 := program.property
  rw [pure_value]
  simpa only [List.append_assoc] using
    window (headerBytes kind ++ profile.val ++ release.val) program.val payment.val 72 j
      (by simp [headerBytes,hp,hr]) lower (by omega)
#print axioms program

theorem payment (profile release program : Bytes32) (kind : U8) (payment : Payment)
    (j : Nat) (lower : 104 ≤ j) (upper : j < 320) :
    (pure profile release program kind payment).val[j]? = payment.val[j-104]? := by
  have hp : profile.val.length = 32 := profile.property
  have hr : release.val.length = 32 := release.property
  have hb : program.val.length = 32 := program.property
  have ht : payment.val.length = 216 := payment.property
  rw [pure_value]
  simpa only [List.append_nil,List.append_assoc] using
    window (headerBytes kind ++ profile.val ++ release.val ++ program.val) payment.val [] 104 j
      (by simp [headerBytes,hp,hr,hb]) lower (by omega)
#print axioms payment
end NFV_RequestIndexes
#print Aeneas.Std.core.array.equality.PartialEqArray.eq
#print Aeneas.Std.core.cmp.PartialEqU8
