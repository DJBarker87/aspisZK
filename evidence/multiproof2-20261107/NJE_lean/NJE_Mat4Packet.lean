import NJE_Residue
import NJA_Mat4Cut

set_option autoImplicit false
noncomputable section
namespace NJE_Mat4Packet
open Aeneas Aeneas.Std Result
open NJA_Pow5Cut (Event)

def events (v : Fin 4 → U32) (r : Fin 4) : Event :=
 ⟨1,NJA_Matrix.rowArg v r,0,NJE_Residue.word (NJA_Matrix.rowArg v r)⟩

theorem laws (v : Fin 4 → U32) : NJA_Mat4Cut.CalleeLaws (events v) := by
 intro r
 exact NJE_Residue.value _

theorem domains (v : Fin 4 → U32) : ∀ r,
    (events v r).a<2^62 ∧ (events v r).out.val<2147483647 := by
 intro r
 exact ⟨NJA_Matrix.argument_bound v r,NJE_Residue.canonical _⟩

theorem TX1_302 (v : Fin 4 → U32) (len : Nat) (post : Fin 4 → U32)
    (cut : NJA_Mat4Cut.Cut v (events v) len post) :
    ∀ r, (post r).val<2147483647 ∧
      ((post r).val : NJA_Matrix.K) = R0P.poseidonMat4 (fun i => ((v i).val : NJA_Matrix.K)) r :=
 NJA_Mat4Cut.compose v (events v) len post cut (laws v)

#print laws
#print axioms laws
#print domains
#print axioms domains
#print TX1_302
#print axioms TX1_302
end NJE_Mat4Packet
end
