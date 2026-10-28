import R1Z.PV_FXM_ZeroWorld
set_option autoImplicit false
namespace R1Z.PV_RJDec_ZeroizeFinding
open PV_FXM_ZeroWorld

/-- Counts certified by the retained LLVM diagnostic for the reached 1.9.0
byte helper, built on deployed rustc/features/release settings. These are
finite diagnostic data, not a formal semantics of LLVM or arbitrary Rust. -/
def inspectedByteCompilerFences : Nat := 0
def inspectedArray32CompilerFences : Nat := 0
def inspectedByteAsmBarriers : Nat := 1
def inspectedArray32AsmBarriers : Nat := 32

/-- The retained model adds a compiler-fence event even for an already-zero
byte. It cannot literally match the inspected source/IR primitive schedule.
An observation-preserving abstraction of the new barrier needs its own proof. -/
theorem byte_fence_mismatch {F : Type} (a : Nat) (w : World F) :
    (native a 1 w).fences ≠ w.fences + inspectedByteCompilerFences := by
  rw [(counts a 1 w).2]
  simp only [inspectedByteCompilerFences,Nat.add_zero]
  omega

theorem array32_fence_mismatch {F : Type} (a : Nat) (w : World F) :
    (native a 32 w).fences ≠ w.fences + inspectedArray32CompilerFences := by
  rw [(counts a 32 w).2]
  simp only [inspectedArray32CompilerFences,Nat.add_zero]
  omega

#print axioms byte_fence_mismatch
#print axioms array32_fence_mismatch
end R1Z.PV_RJDec_ZeroizeFinding
