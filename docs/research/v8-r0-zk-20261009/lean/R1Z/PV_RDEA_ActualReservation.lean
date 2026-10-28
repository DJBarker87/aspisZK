import R1Z.ProverRwFullFuns
import R1Z.PV_CBL_AppendBundle
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEA_ActualReservation
variable [ExternalTypes] [ExternalFuns]

def finiteByte (b : U8) : Fin 256 := ⟨b.val,by
  have h := b.hSize
  norm_num [UScalar.size,UScalarTy.numBits] at h
  exact h⟩
def digestList (digest : Array U8 32#usize) : List (Fin 256) := digest.val.map finiteByte

theorem array_length (digest : Array U8 32#usize) : digest.val.length=32 := by
  cases digest with
  | mk xs h => exact h

theorem digest_length (digest : Array U8 32#usize) : (digestList digest).length=32 := by
  simp only [digestList,List.length_map,array_length]

def suffixText : Str := toStr ".burn" (by rw [String.size_toByteArray]; change 5≤U32.max; norm_num [U32.max,U32.numBits])

/-- Concrete extracted endpoint tail, rather than an arbitrary continuation. -/
theorem at_end (digest : Array U8 32#usize) (acc : String) :
    aspis_prover.state_only_entropy.reservation_name digest acc 32#usize =
      ExternalFuns.op31 acc suffixText := by
  rw [aspis_prover.state_only_entropy.reservation_name.eq_def]
  simp only [if_true]
  rfl

#print axioms array_length
#print axioms digest_length
#print axioms at_end
end R1Z.PV_RDEA_ActualReservation
