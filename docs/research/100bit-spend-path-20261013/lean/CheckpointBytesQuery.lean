import CheckpointBytesWord

set_option autoImplicit false
namespace AspisR1.CheckpointBytesQuery
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted CheckpointBytesBodyArithmetic CheckpointBytesWord
open OraclePortCompactDraft
attribute [local irreducible] body_byte

theorem query_dispatch (p : aspis_r1_cost_probe.verifier.Prepared)
    (a : aspis_r1_cost_probe.verifier.Accumulator) (hp hu : Array U8 32#usize)
    (j : Fin 22) (i : Usize) (bound : i.val < 4) :
    body_byte p a hp hu (Usize.ofNat (320+4*j.val+i.val) (by have := j.isLt; scalar_tac)) =
      select (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)) i := by
  have indexBound := j.isLt
  let at1 := Usize.ofNat (320+4*j.val+i.val) (by scalar_tac)
  have value : at1.val = 320+4*j.val+i.val := by simp [at1]
  have h8 : ¬ at1 < 8#usize := by scalar_tac
  have h16 : ¬ at1 < 16#usize := by scalar_tac
  have h48 : ¬ at1 < 48#usize := by scalar_tac
  have h80 : ¬ at1 < 80#usize := by scalar_tac
  have h112 : ¬ at1 < 112#usize := by scalar_tac
  have h176 : ¬ at1 < 176#usize := by scalar_tac
  have h304 : ¬ at1 < 304#usize := by scalar_tac
  have h320 : ¬ at1 < 320#usize := by scalar_tac
  have h408 : at1 < 408#usize := by scalar_tac
  change body_byte p a hp hu at1 = _
  simp only [body_byte,if_neg h8,if_neg h16,if_neg h48,if_neg h80,
    if_neg h112,if_neg h176,if_neg h304,if_neg h320,if_pos h408]
  have quotient : (320+4*j.val+i.val-320)/4 = j.val := by omega
  have remainder : (320+4*j.val+i.val-320)%4 = i.val := by omega
  simp (disch := scalar_tac) [Array.index_usize,p.queries.property,
    sub_exact,div_exact,rem_exact,value,quotient,remainder,select,Nat.mod_eq_of_lt bound]

theorem query_bytes (p : aspis_r1_cost_probe.verifier.Prepared)
    (a : aspis_r1_cost_probe.verifier.Accumulator) (hp hu : Array U8 32#usize)
    (j : Fin 22) (i : Usize) (bound : i.val < 4) :
    ∃ v, body_byte p a hp hu (Usize.ofNat (320+4*j.val+i.val) (by have := j.isLt; scalar_tac)) = ok v ∧
      (le32 (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val)[i.val]? =
        some (AspisV8R19.SqueezeOracleBridge.decodeByte v) := by
  rw [query_dispatch p a hp hu j i bound]
  exact select_bytes _ i bound

#print axioms query_dispatch
#print axioms query_bytes
end AspisR1.CheckpointBytesQuery
