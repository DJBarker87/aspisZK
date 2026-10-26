import Std
set_option autoImplicit false
namespace R1Z.PV_PoleMaskPartition
-- A symbolic bijection, with no enumeration of the 1024 native rows.
def unpack (row : Fin 1024) : Fin 64 × Fin 16 :=
  (⟨row.val/16,by have h:=row.isLt; omega⟩,
   ⟨row.val%16,Nat.mod_lt _ (by decide)⟩)

def pack (cell : Fin 64 × Fin 16) : Fin 1024 :=
  ⟨16*cell.1.val+cell.2.val,by
    have hb:=cell.1.isLt
    have hi:=cell.2.isLt
    omega⟩

theorem pack_unpack (row : Fin 1024) : pack (unpack row)=row := by
  apply Fin.ext
  dsimp only [pack,unpack]
  omega

theorem unpack_pack (cell : Fin 64 × Fin 16) : unpack (pack cell)=cell := by
  have hb:=cell.1.isLt
  have hi:=cell.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> dsimp only [pack,unpack] <;> omega

#print axioms pack_unpack
#print axioms unpack_pack
end R1Z.PV_PoleMaskPartition
