import NJA_Matrix
import NJA_ChunkFrame

set_option autoImplicit false
noncomputable section
namespace NJA_External
open Aeneas Aeneas.Std Result
open NJA_ChunkFrame
abbrev K := NJA_Matrix.K

def columnSum (v : State U32) (c : Fin 4) : Nat :=
 (((0+(v (pack 0 c)).val)+(v (pack 1 c)).val)+(v (pack 2 c)).val)+(v (pack 3 c)).val

def arg (v : State U32) (i : Fin 16) : Nat := (v i).val + columnSum v (column i)

theorem column_bound (v : State U32) (c : Fin 4) : columnSum v c < 2^35 := by
 have h0 := (v (pack 0 c)).bv.isLt
 have h1 := (v (pack 1 c)).bv.isLt
 have h2 := (v (pack 2 c)).bv.isLt
 have h3 := (v (pack 3 c)).bv.isLt
 change (v (pack 0 c)).val < 2^32 at h0
 change (v (pack 1 c)).val < 2^32 at h1
 change (v (pack 2 c)).val < 2^32 at h2
 change (v (pack 3 c)).val < 2^32 at h3
 unfold columnSum
 omega

theorem arg_bound (v : State U32) (i : Fin 16) : arg v i < 2^62 := by
 have h := column_bound v (column i)
 have b := (v i).bv.isLt
 change (v i).val < 2^32 at b
 unfold arg
 omega

def word (v : State U32) (i : Fin 16) : U64 := ⟨BitVec.ofNat 64 (arg v i)⟩

theorem word_value (v : State U32) (i : Fin 16) : (word v i).val = arg v i := by
 change arg v i % 2^64 = arg v i
 apply Nat.mod_eq_of_lt
 have := arg_bound v i
 omega

theorem column_cast (v : State U32) (c : Fin 4) : (columnSum v c : K) =
 (((0+((v (pack 0 c)).val:K))+((v (pack 1 c)).val:K))+((v (pack 2 c)).val:K))+((v (pack 3 c)).val:K) := by
 simp [columnSum]

theorem callee (v : State U32) (i : Fin 16) : ∃ z : U32,
 AspisR1SelectedMaskProbe.field.M31.reduce_u62 (word v i) = ok z ∧
 z.val<2147483647 ∧ (z.val:K) = ((v i).val:K)+(columnSum v (column i):K) := by
 obtain ⟨z,hz,vz,cz⟩ := NJA_FieldLaws.reduce_u62 (word v i)
 refine ⟨z,hz,cz,?_⟩
 rw [vz,word_value]
 simp [K,NJA_Matrix.K,AspisV8R15.ExactTowerBase.M31Exact,ZMod.natCast_mod,arg]

theorem model (input cells : State U32)
 (blocks : ∀ g c, ((cells (pack g c)).val:K) =
   R0P.poseidonMat4 (fun j => ((input (pack g j)).val:K)) c)
 (i : Fin 16) :
 ((cells i).val:K)+(columnSum cells (column i):K) =
 R0P.poseidonExternalLinear (fun j => ((input j).val:K)) i := by
 rw [column_cast]
 have same := blocks (group i) (column i)
 rw [pack_parts] at same
 rw [same,blocks,blocks,blocks,blocks]
 rfl

#print axioms column_bound
#print axioms arg_bound
#print axioms word_value
#print axioms column_cast
#print axioms callee
#print axioms model
end NJA_External
end
