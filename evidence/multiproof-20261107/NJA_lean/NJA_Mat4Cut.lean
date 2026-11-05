import NJA_Matrix
import NJA_Pow5Cut

set_option autoImplicit false
noncomputable section
namespace NJA_Mat4Cut
open Aeneas Aeneas.Std Result
open NJA_Pow5Cut (Event)

/-- NJA_poseidon.rs::NJA_mat4_log4: len=4, four exact reduction arguments,
kind=1 and every mutated caller-chunk coordinate equals its SAME logged reply.
No interpreted reply or endpoint equality is in this proposition. The actual
caller chunk has exactly four cells. Token erasure is NJA_POSEIDON_SOURCE.json. -/
def Cut (v : Fin 4 → U32) (events : Fin 4 → Event) (len : Nat)
    (post : Fin 4 → U32) : Prop :=
  len = 4 ∧ ∀ r, (events r).kind = 1 ∧
    (events r).a = NJA_Matrix.rowArg v r ∧ post r = (events r).out

def CalleeLaws (events : Fin 4 → Event) : Prop :=
  ∀ r, (events r).out.val = (events r).a % 2147483647

theorem reduction_determined (x : U64) (reply : U32)
    (value : reply.val = x.val % 2147483647) :
    AspisR1SelectedMaskProbe.field.M31.reduce_u62 x = ok reply := by
  obtain ⟨z,hz,vz,cz⟩ := NJA_FieldLaws.reduce_u62 x
  have eq : z = reply := UScalar.eq_of_val_eq (vz.trans value.symm)
  simpa [eq] using hz

theorem caller_domains (v : Fin 4 → U32) (events : Fin 4 → Event) (len : Nat)
    (post : Fin 4 → U32) (cut : Cut v events len post) :
    ∀ r, (events r).a < 2^62 := by
  intro r
  rw [(cut.2 r).2.1]
  exact NJA_Matrix.argument_bound v r

theorem compose (v : Fin 4 → U32) (events : Fin 4 → Event) (len : Nat)
    (post : Fin 4 → U32) (cut : Cut v events len post) (laws : CalleeLaws events) :
    ∀ r, (post r).val < 2147483647 ∧
      ((post r).val : NJA_Matrix.K) = R0P.poseidonMat4 (fun i => ((v i).val : NJA_Matrix.K)) r := by
  intro r
  have args := (cut.2 r).2.1
  have out := (cut.2 r).2.2
  have red := reduction_determined (NJA_Matrix.argument v r) (post r) (by
    rw [NJA_Matrix.argument_value, out, laws r, args])
  obtain ⟨z,hz,cz,mz⟩ := NJA_Matrix.row_value v r
  have eq : z = post r := Result.ok.inj (hz.symm.trans red)
  simpa [eq] using And.intro cz mz

#print axioms reduction_determined
#print axioms caller_domains
#print axioms compose
end NJA_Mat4Cut
end
