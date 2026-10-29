import R1Merkle32Leaf
import NDH_ArrayIndex
set_option autoImplicit false
namespace NDH_MerkleGrammar
open Aeneas Aeneas.Std Result
open AspisR1

def byte (x : U8) : Fin 256 := ⟨x.val,x.bv.isLt⟩

def row (c : Array (Array U8 32#usize) 8#usize) (i : Fin 8) : Array U8 32#usize :=
  c.val[i.val]'(by have := c.property; change c.val.length=8 at this; omega)

def children (c : Array (Array U8 32#usize) 8#usize) : Merkle32Path.Children :=
  fun i j => byte ((row c i).val[j.val]'(by
    have h := (row c i).property
    change (row c i).val.length=32 at h
    omega))

theorem row_ofFn (a : Array U8 32#usize) :
    a.val.map byte = List.ofFn (fun j : Fin 32 =>
      byte (a.val[j.val]'(by have := a.property; change a.val.length=32 at this; omega))) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn]
    exact a.property
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]

theorem chunks (c : Array (Array U8 32#usize) 8#usize) :
    (List.ofFn (fun i : Fin 8 => (row c i).val.map byte)).flatten =
      Merkle32Path.nodeBytes (children c) := by
  unfold Merkle32Path.nodeBytes
  rw [List.ofFn_mul (m:=8) (n:=32)]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [row_ofFn]
  apply congrArg List.ofFn
  funext j
  have hd : (i.val*32+j.val)/32=i.val := by omega
  have hm : (i.val*32+j.val)%32=j.val := by omega
  simp only [Merkle32Path.childByte, children, hd, hm]

def sourceNode (c : Array (Array U8 32#usize) 8#usize) : List (Fin 256) :=
  24 :: (List.ofFn (fun i : Fin 8 => (row c i).val.map byte)).flatten

theorem node (c : Array (Array U8 32#usize) 8#usize) :
    sourceNode c = Merkle32Path.nodeInput (children c) := by
  unfold sourceNode Merkle32Path.nodeInput
  rw [chunks]

#print axioms row_ofFn
#print axioms chunks
#print axioms node
end NDH_MerkleGrammar
