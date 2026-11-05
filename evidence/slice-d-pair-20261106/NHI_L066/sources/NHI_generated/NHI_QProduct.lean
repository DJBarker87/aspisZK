import NHI_ScalarStep
set_option autoImplicit false
noncomputable section
namespace NHI_QProduct
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
attribute [local instance] Classical.propDecidable

def mul (x q : NQ) : NQ :=
 if h : canonQ x ∧ canonQ q then Classical.choose (LPi_TowerValues.qm_mul x q h.1 h.2)
 else FIo_Native.aspis_core.field.QM31.ZERO

theorem spec (x q : NQ) (hx : canonQ x) (hq : canonQ q) :
 FIo_Native.aspis_core.field.QM31.mul x q=ok (mul x q) ∧ canonQ (mul x q) ∧
 qw (mul x q)=mulQ (qw x) (qw q) := by
 simp only [mul,dif_pos (show canonQ x ∧ canonQ q from ⟨hx,hq⟩)]
 exact Classical.choose_spec (LPi_TowerValues.qm_mul x q hx hq)

def sliceAt (s : Slice NQ) (i : Nat) : NQ := s.val[i]?.getD FIo_Native.aspis_core.field.QM31.ZERO
def arrayAt {n : Usize} (a : Array NQ n) (i : Nat) : NQ := a.val[i]?.getD FIo_Native.aspis_core.field.QM31.ZERO

theorem slice_at (s : Slice NQ) (i : Usize) (x : NQ) (run : Slice.index_usize s i=ok x) :
 sliceAt s i.val=x := by
 unfold Slice.index_usize at run
 split at run
 · cases run
 · rename_i v read
   cases Result.ok.inj run
   change s.val[i.val]?=some x at read
   simp only [sliceAt,read,Option.getD_some]

theorem array_at {n : Usize} (a : Array NQ n) (i : Usize) (x : NQ) (run : Array.index_usize a i=ok x) :
 arrayAt a i.val=x := by
 unfold Array.index_usize at run
 split at run
 · cases run
 · rename_i v read
   cases Result.ok.inj run
   change a.val[i.val]?=some x at read
   simp only [arrayAt,read,Option.getD_some]

#print axioms spec
#print axioms slice_at
#print axioms array_at
end NHI_QProduct
end
