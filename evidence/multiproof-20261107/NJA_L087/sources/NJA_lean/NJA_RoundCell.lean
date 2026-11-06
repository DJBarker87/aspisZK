import NJA_Compress
import NJA_Pow5Model
import NJA_PointFrame

set_option autoImplicit false
noncomputable section
namespace NJA_RoundCell
open Aeneas Aeneas.Std Result
abbrev K := NJA_Matrix.K

def reference (x c : U32) : Result U32 := do
 let input ← AspisR1SemanticCallExtraction.aspis_core.field.M31.add x c
 NJA_FieldLaws.pow5_ref input

theorem total (x c : U32) (hx : x.val<2147483647) (hc : c.val<2147483647) :
 ∃ z : U32, reference x c = ok z ∧ z.val<2147483647 ∧
 (z.val:K) = R0P.poseidonPow5 ((x.val:K)+(c.val:K)) := by
 obtain ⟨input,hi,ci,vi⟩ := NJA_Compress.add_law x c hx hc
 obtain ⟨z,hz,cz,vz⟩ := NJA_Pow5Model.reference input
 refine ⟨z,?_,cz,?_⟩
 · simp only [reference,hi,hz,bind_tc_ok]
 · rw [vz,vi]

theorem full_cells (s c : Fin 16 → K) :
 NJA_PointFrame.run s (fun i x => R0P.poseidonPow5 (x+c i)) 16 =
   fun i => R0P.poseidonPow5 (s i+c i) :=
 NJA_PointFrame.complete _ _

theorem full_round (s c : Fin 16 → K) :
 R0P.poseidonExternalLinear (NJA_PointFrame.run s (fun i x => R0P.poseidonPow5 (x+c i)) 16) =
 R0P.poseidonFullRound s c := by
 rw [full_cells]
 rfl

theorem internal_cell (s : Fin 16 → K) (c : K) :
 NJA_PointFrame.write s 0 (R0P.poseidonPow5 (s 0+c)) =
 fun i => if i=0 then R0P.poseidonPow5 (s 0+c) else s i := rfl

theorem internal_round (s : Fin 16 → K) (c : K) :
 R0P.poseidonInternalLinear (NJA_PointFrame.write s 0 (R0P.poseidonPow5 (s 0+c))) =
 R0P.poseidonInternalRound s c := rfl

#print axioms total
#print axioms full_cells
#print axioms full_round
#print axioms internal_cell
#print axioms internal_round
end NJA_RoundCell
end
