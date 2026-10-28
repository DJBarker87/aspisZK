import PV_L2C_DigestOrigin
import R1Z.BuilderRecordCanonical
set_option autoImplicit false
namespace PV_L2C_DigestEncode
open Aeneas Aeneas.Std Result R0Z.WriterRefine AspisR1TerminalDecoder

def encode (d : Array U32 8#usize) : Array U8 32#usize :=
  ⟨List.ofFn (fun j : Fin 32 => (core.num.U32.to_le_bytes d.val[j.val/4]!).val[j.val%4]!),by simp⟩

theorem byte (d : Array U32 8#usize) (j : Nat) (hj : j < 8) (k : Nat) (hk : k < 4) :
    (encode d).val[4*j+k]! = (core.num.U32.to_le_bytes d.val[j]!).val[k]! := by
  unfold encode
  rw [List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,dif_pos (by omega)]
  simp only [Option.getD_some]
  have hdiv : (4*j+k)/4 = j := by omega
  have hmod : (4*j+k)%4 = k := by omega
  rw [hdiv,hmod]
#print axioms byte

def limb (b : Array U8 32#usize) (j : Nat) : Array U8 4#usize :=
  Array.make 4#usize [b.val[4*j]!,b.val[4*j+1]!,b.val[4*j+2]!,b.val[4*j+3]!]

theorem limb_encoded (d : Array U32 8#usize) (j : Nat) (hj : j < 8) :
    limb (encode d) j = core.num.U32.to_le_bytes d.val[j]! := by
  apply R1Z.BuilderRecordCanonical.array_ext
  intro k hk
  have hk' : k < 4 := by simpa using hk
  interval_cases k <;> simp only [limb,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ]
  all_goals first
    | exact byte d j hj 0 (by omega)
    | exact byte d j hj 1 (by omega)
    | exact byte d j hj 2 (by omega)
    | exact byte d j hj 3 (by omega)
#print axioms limb_encoded

theorem scalar (d : Array U32 8#usize) (hd : Canon8 d) (j : Nat) (hj : j < 8) :
    aspis_core.field.M31.from_le_bytes (limb (encode d) j) = ok (some d.val[j]!) := by
  rw [PV_L2C_DigestRange.scalar_eq,limb_encoded d j hj]
  exact PV_L2C_CanonicalParser.scalar_parse _ (hd j hj)
#print axioms scalar
end PV_L2C_DigestEncode
