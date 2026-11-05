import NHG_COMBINED_IMPORT
import RPv_JFy_Pow5
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Pow5
open FIq_Native
open FIv_NativeValue (Canon decode)
abbrev Q := field.QM31

def body (square : Q→Result Q) (mul : Q→Q→Result Q) (x : Q) : Result Q := do
 let x2←square x
 let x4←square x2
 mul x4 x

theorem source (x : Q) : state_only_poseidon.pow5 x=body field.QM31.square field.QM31.mul x := rfl

theorem result (x : Q) (canonical : Canon x) :
 ∃ out,state_only_poseidon.pow5 x=ok out ∧ Canon out ∧ decode out=decode x^5 :=
 JFy_Pow5.source x canonical

theorem domains (x : Q) (canonical : Canon x) :
 ∃ x2 x4,field.QM31.square x=ok x2 ∧ Canon x2 ∧
 field.QM31.square x2=ok x4 ∧ Canon x4 := by
 obtain ⟨x2,first,canon2,_⟩:=JFy_SquareTotal.source x canonical
 obtain ⟨x4,second,canon4,_⟩:=JFy_SquareTotal.source x2 canon2
 exact ⟨x2,x4,first,canon2,second,canon4⟩
#print axioms source
#print axioms result
#print axioms domains
end AspisR1.NHU_Pow5
end
