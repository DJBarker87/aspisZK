import PCF_LaneValue
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_WordBridge

def word (x : U32) : UInt32 := UInt32.ofNat x.val

theorem word_value (x : U32) : (word x).toNat = x.val := by
  have h : x.val < 4294967296 := by scalar_tac
  simpa only [word, UInt32.toNat_ofNat'] using Nat.mod_eq_of_lt h

def byte (x : U8) : UInt8 := UInt8.ofNat x.val

theorem byte_value (x : U8) : (byte x).toNat = x.val := by
  have h : x.val < 256 := by scalar_tac
  simpa only [byte, UInt8.toNat_ofNat'] using Nat.mod_eq_of_lt h

#print axioms word_value
#print axioms byte_value
end PCF_WordBridge
