import FIn_ExtractFuns
import FIn_Polynomial
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_ExtractInstall
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

def arithmetic : FIn_Extract.FIn_reference.Arithmetic Unit E where
  coremarkerCopyInst := ⟨⟨fun x => ok x⟩⟩
  zero := ok FIn_Polynomial.zero
  mul := FIn_Polynomial.mul
  add := FIn_Primitives.add
  field := FIn_Primitives.field

def polynomial := FIn_Extract.FIn_reference.polynomial arithmetic

theorem same (bytes : Slice U8) (x : E) :
    polynomial bytes x = FIn_Polynomial.polynomial bytes x := by
  simp only [polynomial,FIn_Extract.FIn_reference.polynomial,arithmetic,
    FIn_Polynomial.polynomial,FIn_Polynomial.go,bind_tc_ok]

#print axioms same
end AspisR1.FIn_ExtractInstall
end
