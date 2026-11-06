import NJE_Mat4Packet
import NJA_ChunkFrame

set_option autoImplicit false
noncomputable section
namespace NJE_ExternalBlocks
open Aeneas Aeneas.Std Result NJA_ChunkFrame
abbrev K := NJA_Matrix.K

def matrix (v : Fin 4 → U32) (r : Fin 4) : U32 := NJE_Residue.word (NJA_Matrix.rowArg v r)
def blocks (v : State U32) : State U32 := fun i => matrix (block v (group i)) (column i)

theorem matrix_value (v : Fin 4 → U32) (r : Fin 4) :
    (matrix v r).val<2147483647 ∧
    ((matrix v r).val:K)=R0P.poseidonMat4 (fun j => ((v j).val:K)) r := by
 have cut : NJA_Mat4Cut.Cut v (NJE_Mat4Packet.events v) 4 (matrix v) := by
   constructor
   · rfl
   · intro i; exact ⟨rfl,rfl,rfl⟩
 exact NJE_Mat4Packet.TX1_302 v 4 (matrix v) cut r

theorem block_value (v : State U32) (g c : Fin 4) :
    ((blocks v (pack g c)).val:K)=
      R0P.poseidonMat4 (fun j => ((v (pack g j)).val:K)) c := by
 simp only [blocks,group_pack,column_pack,block]
 exact (matrix_value _ _).2

theorem canonical (v : State U32) (i : Fin 16) : (blocks v i).val<2147483647 :=
 (matrix_value _ _).1

theorem chronology (v : State U32) : run v matrix 4 = blocks v := complete v matrix

#print matrix_value
#print axioms matrix_value
#print block_value
#print axioms block_value
#print canonical
#print axioms canonical
#print chronology
#print axioms chronology
end NJE_ExternalBlocks
end
