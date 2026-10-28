import R1Z.PV_RDB2_CBL_GenericArrayPower
import R1Z.PV_RDB2_CBL_PadListFacts
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_StorageBuild
open PV_CBL_GenericArrayPower
set_option autoImplicit false

/-- Construct the actual recursively nested GenericArray storage, with the
left half before the right half and no unsafe initialization. -/
def build {T : Type} : (k : Nat) → (Nat → T) → Storage T k
  | 0,f => ⟨Array.make 0#usize [],Array.make 0#usize [],f 0⟩
  | k+1,f => ⟨build k f,build k (fun i => f (2^k+i)),()⟩

theorem flatten_build {T : Type} (k : Nat) (f : Nat → T) :
    flatten k (build k f)=List.ofFn (fun i : Fin (2^k) => f i.val) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    change flatten k (build k f)++flatten k (build k (fun i => f (2^k+i)))=_
    rw [ih,ih]
    simp only [Nat.pow_succ,Nat.mul_two,List.ofFn_add]
    rfl

theorem reconstruct {T : Type} [Inhabited T] (k : Nat) (xs : List T)
    (h : xs.length=2^k) :
    flatten k (build k (fun i => xs[i]!))=xs := by
  rw [flatten_build]
  apply List.ext_getElem?
  intro i
  by_cases hi : i<2^k
  · have hx : i<xs.length := by omega
    rw [List.getElem?_ofFn]
    simp only [dif_pos hi]
    rw [List.getElem?_eq_getElem hx,PV_CBL_PadListFacts.get_bang xs i hx]
  · rw [List.getElem?_ofFn]
    simp only [dif_neg hi]
    exact (List.getElem?_eq_none_iff.mpr (by omega)).symm

def from32 (a : Array U8 32#usize) : Storage U8 5 :=
  build 5 (fun i => a.val[i]!)

def to64 (a : Storage U8 6) : Array U8 64#usize :=
  ⟨flatten 6 a,by rw [PV_CBL_GenericArrayPower.length];rfl⟩

theorem from32_value (a : Array U8 32#usize) :
    flatten 5 (from32 a)=a.val :=
  reconstruct 5 a.val a.property

#print axioms build
#print axioms flatten_build
#print axioms reconstruct
#print axioms from32
#print axioms to64
#print axioms from32_value
end R1Z.PV_DL_StorageBuild
