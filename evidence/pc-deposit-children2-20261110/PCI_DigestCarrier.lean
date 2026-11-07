import PCI_ArrayCanonical
import PCI_SingleComplete
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DigestCarrier
open PCI_ValidateCarrier

def digest (d : Array U32 8#usize) : PCA.Digest :=
  ⟨(d.val.map readWord).toArray, by simp only [List.size_toArray,List.length_map];exact d.property⟩

theorem read_value (x : U32) : (readWord x).toNat=x.val := by
  have hx : x.val<4294967296 := by scalar_tac
  simp only [readWord,UInt32.toNat_ofNat',Nat.mod_eq_of_lt hx]

theorem bool_if (p : Prop) [Decidable p] (b : Bool) :
    (if p then b else false)= (decide p && b) := by
  by_cases h : p <;> simp only [h,ite_true,ite_false,decide_true,decide_false,Bool.true_and,Bool.false_and]

theorem canonical (d : Array U32 8#usize) :
    PCI_ArrayCanonical.model d=PCC.canonical (digest d) := by
  rcases d with ⟨l,hl⟩
  change l.length=8 at hl
  cases l with
  | nil => simp only [List.length_nil,List.length_cons] at hl;omega
  | cons a0 t0 =>
    cases t0 with
    | nil => simp only [List.length_nil,List.length_cons] at hl;omega
    | cons a1 t1 =>
      cases t1 with
      | nil => simp only [List.length_nil,List.length_cons] at hl;omega
      | cons a2 t2 =>
        cases t2 with
        | nil => simp only [List.length_nil,List.length_cons] at hl;omega
        | cons a3 t3 =>
          cases t3 with
          | nil => simp only [List.length_nil,List.length_cons] at hl;omega
          | cons a4 t4 =>
            cases t4 with
            | nil => simp only [List.length_nil,List.length_cons] at hl;omega
            | cons a5 t5 =>
              cases t5 with
              | nil => simp only [List.length_nil,List.length_cons] at hl;omega
              | cons a6 t6 =>
                cases t6 with
                | nil => simp only [List.length_nil,List.length_cons] at hl;omega
                | cons a7 t7 =>
                  cases t7 with
                  | cons b t => simp only [List.length_cons] at hl;omega
                  | nil =>
                    simp only [PCI_ArrayCanonical.model,PCC.canonical,digest,Vector.toList,List.toList_toArray,List.map_cons,List.map_nil,List.all_cons,List.all_nil,read_value,List.getElem!_cons_zero,List.getElem!_cons_succ,Bool.and_true,bool_if,Bool.and_assoc]

#print axioms bool_if
#print axioms read_value
#print axioms canonical
end PCI_DigestCarrier
