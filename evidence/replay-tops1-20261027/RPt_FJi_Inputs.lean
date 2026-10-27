import RPt_FJi_Accumulations
import RPt_JFr_TX2_DotStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_Inputs
open Aeneas Aeneas.Std Result
open FJi_Accumulations
/-- Installed to_limbs order, on the SAME selected wide coefficient. -/
def limbs (x : NE) : Coefficients := Array.make 8#usize
  [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]
abbrev read := JFr_TX2_ScalarRead.read
/-- Total observation used only after its successful read has been derived. -/
def scalar (q : Array U8 608#usize) (slot term : Usize) : U32 :=
  match read q slot term with
  | .ok x => x
  | _ => 0#u32

def coefficient (g : Array NE 29#usize) (term j : Nat) : U32 :=
  match g.val[term]? with
  | some x => (limbs x).val[j]?.getD 0#u32
  | none => 0#u32

def cursor (n : Nat) : Usize := Usize.ofNat (n%26) (by have h:=Nat.mod_lt n (by decide : 0<26); scalar_tac)

def product (q : Array U8 608#usize) (g : Array NE 29#usize)
    (slot : Usize) (j n : Nat) : Nat :=
  (coefficient g n j).val*(scalar q slot (cursor n)).val

theorem cursor_same (t : Usize) (ht : t.val<26) : cursor t.val=t := by
  apply UScalar.eq_of_val_eq
  change t.val%26=t.val
  exact Nat.mod_eq_of_lt ht

theorem scalar_value (q : Array U8 608#usize) (slot term : Usize) (x : U32)
    (run : read q slot term=ok x) : scalar q slot term=x := by
  simp only [scalar,run]

theorem coefficient_value (g : Array NE 29#usize) (term : Usize) (x : NE)
    (run : Array.index_usize g term=ok x) (j : Nat) :
    coefficient g term.val j=(limbs x).val[j]?.getD 0#u32 := by
  simp only [coefficient,FJc_ReadSlot.slot g term x run]

theorem to_limbs (x : NE) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x=ok (limbs x) := rfl

theorem update (g : Array NE 29#usize) (term : Usize) (a : U32) (s : Sums) :
    JFr_TX2_DotStep.update g term a s=(do
      let x ← Array.index_usize g term
      accumulate (limbs x) a s) := by
  simp only [JFr_TX2_DotStep.update,accumulate,to_limbs,bind_tc_ok,bind_assoc_eq]
#print axioms cursor_same
#print axioms scalar_value
#print axioms coefficient_value
#print axioms to_limbs
#print axioms update
end AspisR1.FJi_Inputs
end
