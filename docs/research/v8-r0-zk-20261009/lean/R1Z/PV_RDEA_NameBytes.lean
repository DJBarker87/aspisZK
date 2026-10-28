import R1Z.PV_RDEA_AppendNoGrowth
import R1Z.PV_RDEA_ReservationName
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_NameBytes
open PV_RDEA_ReservationName

def digitByte (n : Fin 16) : U8 := U8.ofNatCore (digit n) (by
  have h := n.isLt
  unfold digit
  split <;> omega)

theorem digit_byte_value (n : Fin 16) : (digitByte n).val=digit n := rfl

theorem digit_table : ∀ n : Fin 16, digit n =
    ([48,49,50,51,52,53,54,55,56,57,97,98,99,100,101,102][n.val]?).getD 0 := by
  decide

def suffix : List U8 := [46#u8,98#u8,117#u8,114#u8,110#u8]
def bytes : List (Fin 256) → List U8
  | [] => suffix
  | b::rest => digitByte (high b)::digitByte (low b)::bytes rest

theorem byte_length (digest : List (Fin 256)) : (bytes digest).length=2*digest.length+5 := by
  induction digest with
  | nil => rfl
  | cons b bs ih => simp only [bytes,List.length_cons,ih]; omega

theorem byte_not_slash (n : Fin 16) : digitByte n≠47#u8 := by
  intro h
  have hv := congrArg (fun x : U8 => x.val) h
  exact digit_not_slash n hv

theorem no_slash (digest : List (Fin 256)) : 47#u8 ∉ bytes digest := by
  induction digest with
  | nil => decide
  | cons b bs ih =>
    simp only [bytes,List.mem_cons,not_or]
    exact ⟨Ne.symm (byte_not_slash _),Ne.symm (byte_not_slash _),ih⟩

#print axioms digit_byte_value
#print axioms digit_table
#print axioms byte_length
#print axioms byte_not_slash
#print axioms no_slash
end R1Z.PV_RDEA_NameBytes
