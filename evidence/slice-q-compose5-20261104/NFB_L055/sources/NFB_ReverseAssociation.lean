import NFB_ReverseTrace
import NEW_GeometryRawHelpers
set_option autoImplicit false
noncomputable section
namespace NFB_ReverseAssociation
open Aeneas Aeneas.Std Result AspisR1
open NEW_GeometryRawInterface NFB_PhysicalFrame NFB_PrivateFrame

theorem complete (flat prefixes inverse : alloc.vec.Vec U32) (suffix : U32) (index : Usize)
 (bound : index.val≤110) (hf : index.val≤flat.val.length)
 (hp : index.val≤prefixes.val.length) (hi : index.val ≤ inverse.val.length)
 (heap : Heap) (selected : heap Place.inverse.id=some inverse.val) :
 ∃ out : alloc.vec.Vec U32,
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
  (Port4C_Reverse.reverse index) flat prefixes suffix inverse=ok out ∧
 NEW_GeometryReverse.Trace flat.val prefixes.val index.val inverse.val suffix out.val
  (NEW_GeometryReverse.suffixAfter flat.val index.val suffix)
  (NEW_GeometryReverse.callLog flat.val prefixes.val index.val suffix) ∧
 NFB_PhysicalFrame.run (NFB_ReverseTrace.writes flat.val prefixes.val index.val suffix)
  heap Place.inverse.id=some out.val ∧
 (∀ count,NFB_PhysicalFrame.run
  ((NFB_ReverseTrace.writes flat.val prefixes.val index.val suffix).take count) heap 0=heap 0) := by
 obtain ⟨out,owned,meaning,length⟩ := Port4C_OwnedInverse.inverse_refines
  flat prefixes inverse suffix index bound hf hp hi
 have multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := by
  funext x y
  exact NEW_GeometryArithmetic.multiply_probe x y
 have native := Port4C_InverseLoop.from_owned ops multiply flat prefixes inverse out suffix index bound owned
 have trace := NFB_ReverseTrace.complete flat.val prefixes.val inverse.val index.val suffix hi
 have physical := NFB_ReverseTrace.payload flat.val prefixes.val inverse.val index.val suffix heap selected
 refine ⟨out,?_,?_,?_,?_⟩
 · rw [NEW_GeometryRawHelpers.backward]
   exact native
 · rw [meaning]
   exact trace
 · rw [meaning]
   exact physical
 · exact fun count=>protected_query _ heap count (NFB_ReverseTrace.owned _ _ _ _)
#print axioms complete
end NFB_ReverseAssociation
end
