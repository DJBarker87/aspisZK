import FJj_QMSlice
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorPrefix
open Aeneas Aeneas.Std
open FIo_FieldBridge (NQ)

def rowValue (row : Array (Array NQ 4#usize) 5#usize) (d s : Nat) : OraclePortCheckpointAbiC5.K :=
  match row.val[d]? with | some digit=>FJf_QMArray.value digit s | none=>0

def prefix {R : Type} [CommRing R] (g : Nat → Nat → R) : Nat → Nat → R
  | 0,_ => 1
  | m+1,j => prefix g m (j%4^m)*g (m+2) (j/4^m)

theorem read (row : Array (Array NQ 4#usize) 5#usize) (d : Usize)
    (digit : Array NQ 4#usize) (hd : Array.index_usize row d=Result.ok digit) (s : Nat) :
    rowValue row d.val s=FJf_QMArray.value digit s := by
  simp only [rowValue,FJc_ReadSlot.slot _ _ _ hd]

theorem three {R : Type} [CommRing R] (g : Nat → Nat → R) (j : Nat) :
    prefix g 3 j=g 2 (j%4)*g 3 (j/4%4)*g 4 (j/16) := by
  simp only [prefix,pow_zero,pow_one,show 4^2=16 from by decide,
    Nat.mod_one,Nat.div_one,one_mul]
  have h0 : j%16%4=j%4 := by omega
  have h1 : j%16/4=j/4%4 := by omega
  rw [h0,h1]
#print axioms read
#print axioms three
end AspisR1.FJj_TensorPrefix
end
