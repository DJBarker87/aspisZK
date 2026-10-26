import GSProtocolBasisSizesM10

/-! Keep protocol basis construction at runtime. In particular the compiler
must not evaluate six million monomials as a closed term while checking a
cost wrapper. The definition remains transparent to the kernel and has the
same value; no recursion/heartbeat/memory limit is raised. -/
set_option autoImplicit false
namespace AspisR1.GSProtocolBasisMirrorM10

@[never_extract, noinline] def basis (d D ell : Nat) : Array CompPoly.CBivariate.Monomial :=
  AspisWide.GSInterpolationRowBasis.basis d D ell

theorem value (d D ell : Nat) : basis d D ell = AspisWide.GSInterpolationRowBasis.basis d D ell := rfl

theorem initial_size : (basis 1024 114689 112).size = 6480098 := GSProtocolBasisSizesM10.initial
theorem final_size : (basis 255 28673 112).size = 1626522 := GSProtocolBasisSizesM10.final

#print axioms value
#print axioms initial_size
#print axioms final_size
end AspisR1.GSProtocolBasisMirrorM10
