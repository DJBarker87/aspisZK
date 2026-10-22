import CheckpointBytesBodyArithmetic

set_option autoImplicit false
namespace AspisR1.CheckpointBytesHeader
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted CheckpointBytesBodyArithmetic
attribute [local irreducible] body_byte

theorem next_cast (x : Usize) (next : x.val = 10) : UScalar.cast .U8 x = 10#u8 := by
  apply UScalar.eq_of_val_eq
  change ((x.bv).setWidth 8).toNat = 10
  rw [BitVec.toNat_setWidth]
  change x.val % 256 = 10
  omega

theorem header_bytes (p : aspis_r1_cost_probe.verifier.Prepared)
    (a : aspis_r1_cost_probe.verifier.Accumulator) (hp hu : Array U8 32#usize)
    (next : a.next.val = 10) (i : Fin 16) :
    ∃ v, body_byte p a hp hu (Usize.ofNat i.val (by have := i.isLt; scalar_tac)) = ok v ∧
      (OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0])[i.val]? =
        some (AspisV8R19.SqueezeOracleBridge.decodeByte v) := by
  have hc := next_cast a.next next
  fin_cases i <;>
    simp (disch := scalar_tac) [body_byte,Array.index_usize,Array.make,hc,lift,
      sub_exact,OraclePortPhysicalFrameDraft.magic,AspisV8R19.SqueezeOracleBridge.decodeByte]

#print axioms next_cast
#print axioms header_bytes
end AspisR1.CheckpointBytesHeader
