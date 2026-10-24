import R1Z.ProverRwEffectTape

/-! Transparent zeroizing wrapper interpretation at the concrete source
prefix. Installation is explicit; native external contracts are not asserted. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEffectPrefix
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource ProverRwEffectTape
variable [ExternalTypes]

@[reducible] def install (ops : ExternalFuns) : ExternalFuns :=
  { ops with
    op125 := fun inst _ value => inst.as_mut value
    op126 := fun _ value => .ok (value,id)
    op127 := fun _ value => .ok value
    op128 := fun _ value => .ok value }

def back (bytes : Slice U8) : Array U8 64#usize :=
  if h : bytes.length = 64#usize then ⟨bytes.val, by simpa only [Slice.length,Array.length] using h⟩
  else Array.repeat 64#usize 0#u8

theorem fresh_zero (ops : ExternalFuns) :
    @before _ (install ops) = .ok (ProverRwEntropyObstruction.zeroInput,back) := by
  rfl

theorem request (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit retry : Usize)
    (below : retry < limit) :
    @emit _ (install ops) nonce limit retry =
      .read ProverRwEntropyObstruction.zeroInput (@after _ (install ops) nonce retry back) := by
  simp only [emit,below,if_true,fresh_zero]

#print axioms fresh_zero
#print axioms request
end R1Z.ProverRwEffectPrefix
