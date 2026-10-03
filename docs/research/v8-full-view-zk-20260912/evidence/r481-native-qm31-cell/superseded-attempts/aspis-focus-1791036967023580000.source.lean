import AspisV8R19.R174GammaBatchStep

/-! A 128-bit packed cell for the inspected four-lane x86_64 QM31 layout.
This records lane representation only; it is not an ABI or allocation theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R481NativeQM31Cell

open Aeneas Aeneas.Std
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core

def packWords (a b c d : BitVec 32) : BitVec 128 :=
  ((d ++ c) ++ b) ++ a

theorem packWords_lane0 (a b c d : BitVec 32) :
    (packWords a b c d).extractLsb' 0 32 = a := by
  bv_decide

theorem packWords_lane1 (a b c d : BitVec 32) :
    (packWords a b c d).extractLsb' 32 32 = b := by
  bv_decide

theorem packWords_lane2 (a b c d : BitVec 32) :
    (packWords a b c d).extractLsb' 64 32 = c := by
  bv_decide

theorem packWords_lane3 (a b c d : BitVec 32) :
    (packWords a b c d).extractLsb' 96 32 = d := by
  bv_decide

def encodeM31 (x : field.M31) : BitVec 32 := x.bv

def decodeM31 (x : BitVec 32) : field.M31 :=
  U32.ofNat x.toNat x.isLt

def encodeQM31 (x : field.QM31) : BitVec 128 :=
  packWords (encodeM31 x.c0.a) (encodeM31 x.c0.b)
    (encodeM31 x.c1.a) (encodeM31 x.c1.b)

def decodeQM31 (x : BitVec 128) : field.QM31 :=
  { c0 :=
      { a := decodeM31 (x.extractLsb' 0 32)
        b := decodeM31 (x.extractLsb' 32 32) }
    c1 :=
      { a := decodeM31 (x.extractLsb' 64 32)
        b := decodeM31 (x.extractLsb' 96 32) } }

theorem decodeM31_encodeM31 (x : field.M31) : decodeM31 (encodeM31 x) = x := by
  apply U32.bv_eq_imp_eq
  simp [decodeM31, encodeM31, U32.ofNat_bv]

theorem decodeQM31_encodeQM31 (x : field.QM31) : decodeQM31 (encodeQM31 x) = x := by
  cases x with
  | mk c0 c1 =>
    cases c0 with
    | mk a b =>
      cases c1 with
      | mk c d =>
        simp [decodeQM31, encodeQM31, encodeM31, packWords,
          packWords_lane0, packWords_lane1, packWords_lane2, packWords_lane3,
          decodeM31_encodeM31]

#print axioms packWords
#print axioms packWords_lane0
#print axioms packWords_lane1
#print axioms packWords_lane2
#print axioms packWords_lane3
#print axioms encodeM31
#print axioms decodeM31
#print axioms encodeQM31
#print axioms decodeQM31
#print axioms decodeM31_encodeM31
#print axioms decodeQM31_encodeQM31
end AspisV8R19.R481NativeQM31Cell
