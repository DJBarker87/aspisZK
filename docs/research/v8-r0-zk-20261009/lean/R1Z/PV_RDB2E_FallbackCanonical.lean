import R1Z.PV_RDB2E_FallbackScalar

section
-- Unchanged source component R1Z.PV_CBL_FallbackBoolean
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackBoolean
open PV_CBL_FallbackScalar
set_option autoImplicit false
/-- The optimized XOR/AND choose expression equals the conventional SHA choose. -/
theorem choose_eq (x y z : U32) : choose x y z = (x &&& y) ||| ((~~~x) &&& z) := by
  apply U32.bv_eq_imp_eq
  change z.bv ^^^ (x.bv &&& (y.bv ^^^ z.bv)) = (x.bv &&& y.bv) ||| ((~~~x.bv) &&& z.bv)
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_or,
    BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases x.bv.getLsbD i <;> cases y.bv.getLsbD i <;> cases z.bv.getLsbD i <;> decide
theorem majority_eq (x y z : U32) : majority x y z = (x &&& y) ||| (x &&& z) ||| (y &&& z) := by
  apply U32.bv_eq_imp_eq
  change (x.bv &&& y.bv) ^^^ (x.bv &&& z.bv) ^^^ (y.bv &&& z.bv) =
    (x.bv &&& y.bv) ||| (x.bv &&& z.bv) ||| (y.bv &&& z.bv)
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_or,
    BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases x.bv.getLsbD i <;> cases y.bv.getLsbD i <;> cases z.bv.getLsbD i <;> decide
#print axioms choose_eq
#print axioms majority_eq
end R1Z.PV_CBL_FallbackBoolean

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackAddAlgebra
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackAddAlgebra
set_option autoImplicit false
theorem comm (a b : U32) : U32.wrapping_add a b = U32.wrapping_add b a := by
  apply U32.bv_eq_imp_eq
  change a.bv+b.bv=b.bv+a.bv
  exact BitVec.add_comm _ _
theorem assoc (a b c : U32) :
    U32.wrapping_add (U32.wrapping_add a b) c = U32.wrapping_add a (U32.wrapping_add b c) := by
  apply U32.bv_eq_imp_eq
  change (a.bv+b.bv)+c.bv=a.bv+(b.bv+c.bv)
  exact BitVec.add_assoc _ _ _
theorem reverse4 (a b c d : U32) :
    U32.wrapping_add (U32.wrapping_add (U32.wrapping_add a b) c) d =
    U32.wrapping_add (U32.wrapping_add (U32.wrapping_add d c) b) a := by
  apply U32.bv_eq_imp_eq
  change ((a.bv+b.bv)+c.bv)+d.bv=((d.bv+c.bv)+b.bv)+a.bv
  calc
    ((a.bv+b.bv)+c.bv)+d.bv = d.bv+(c.bv+(a.bv+b.bv)) := by
      rw [BitVec.add_comm _ d.bv,BitVec.add_comm (a.bv+b.bv) c.bv]
    _ = (d.bv+c.bv)+(a.bv+b.bv) := (BitVec.add_assoc _ _ _).symm
    _ = (d.bv+c.bv)+(b.bv+a.bv) := by rw [BitVec.add_comm a.bv b.bv]
    _ = ((d.bv+c.bv)+b.bv)+a.bv := (BitVec.add_assoc _ _ _).symm
#print axioms comm
#print axioms assoc
#print axioms reverse4
end R1Z.PV_CBL_FallbackAddAlgebra

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackCanonicalT1
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackCanonicalT1
open PV_CBL_FallbackScalar
set_option autoImplicit false
abbrev ch (e f g : U32) : U32 := (e &&& f) ||| ((~~~e) &&& g)
def value (e f g h w : U32) : U32 :=
  U32.wrapping_add (U32.wrapping_add (U32.wrapping_add h (big1 e)) (ch e f g)) w
theorem source (e f g h w : U32) : t1 e f g h w = value e f g h w := by
  unfold t1 value
  rw [PV_CBL_FallbackBoolean.choose_eq]
  rw [PV_CBL_FallbackAddAlgebra.comm _ h]
  rw [← PV_CBL_FallbackAddAlgebra.assoc h _ w,
    ← PV_CBL_FallbackAddAlgebra.assoc h _ (ch e f g)]
#print axioms ch
#print axioms value
#print axioms source
end R1Z.PV_CBL_FallbackCanonicalT1

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackCanonicalT2
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackCanonicalT2
open PV_CBL_FallbackScalar
set_option autoImplicit false
abbrev maj (a b c : U32) : U32 := (a &&& b) ||| (a &&& c) ||| (b &&& c)
def value (a b c : U32) : U32 := U32.wrapping_add (big0 a) (maj a b c)
theorem source (a b c : U32) : t2 a b c = value a b c := by
  unfold t2 value
  rw [PV_CBL_FallbackBoolean.majority_eq]
#print axioms maj
#print axioms value
#print axioms source
end R1Z.PV_CBL_FallbackCanonicalT2

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackCanonicalStep
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackCanonicalStep
open PV_CBL_FallbackScalar
set_option autoImplicit false
/-- Conventional SHA scalar state transition over wrapping 32-bit words. -/
def step (s : State) (w : U32) : State :=
  let x := PV_CBL_FallbackCanonicalT1.value s.e s.f s.g s.h w
  let y := PV_CBL_FallbackCanonicalT2.value s.a s.b s.c
  ⟨U32.wrapping_add x y,s.a,s.b,s.c,U32.wrapping_add x s.d,s.e,s.f,s.g⟩
theorem source (s : State) (w : U32) : PV_CBL_FallbackScalar.step s w = step s w := by
  simp only [PV_CBL_FallbackScalar.step,step,
    PV_CBL_FallbackCanonicalT1.source,PV_CBL_FallbackCanonicalT2.source]
#print axioms step
#print axioms source
end R1Z.PV_CBL_FallbackCanonicalStep

end
