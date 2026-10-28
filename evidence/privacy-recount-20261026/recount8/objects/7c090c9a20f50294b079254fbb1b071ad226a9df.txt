import R1Z.PDict_Primitives
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Ordering
open Aeneas Aeneas.Std Result ProverRwFull

-- The native Internal marker is a zero-field type and has no runtime data.
def marker : typenum.private.InternalMarker Unit := {}

def lessEq {A B C O : Type} (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessOrEqualPrivate A B C O) (a : A) (b : B) :
    Result O := do
  let order ← cmp.compare marker a b
  next.is_less_or_equal_private a b order

def less {A B C O : Type} (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessPrivate A B C O) (a : A) (b : B) :
    Result O := do
  let order ← cmp.compare marker a b
  next.is_less_private a b order

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { PDict_Primitives.selected ops with op185 := @lessEq, op186 := @less }

theorem op185_installed (ops : ExternalFuns) {A B C O : Type}
    (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessOrEqualPrivate A B C O) (a : A) (b : B) :
    (selected ops).op185 cmp next a b = lessEq cmp next a b := rfl

theorem op186_installed (ops : ExternalFuns) {A B C O : Type}
    (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessPrivate A B C O) (a : A) (b : B) :
    (selected ops).op186 cmp next a b = less cmp next a b := rfl

omit [ExternalTypes] in
theorem compare_failure {A B C O : Type} (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessPrivate A B C O) (a : A) (b : B)
    (e : Error) (failed : cmp.compare marker a b = .fail e) :
    less cmp next a b = .fail e := by
  simp only [less,failed,bind_tc_fail]

#print axioms op185_installed
#print axioms op186_installed
#print axioms compare_failure
end R1Z.PDict_Ordering
