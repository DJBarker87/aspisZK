import R1Z.PV_RDB2E_FallbackScalar
import R1Z.PV_RDB2E_FallbackBlockSwap
import R1Z.PV_RDB2E_FallbackRoundShape
import R1Z.PV_RDB2E_FallbackLanes

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

section
-- Unchanged source component R1Z.PV_CBL_FallbackRoundsModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundsModel
open PV_CBL_FallbackScalar PV_CBL_FallbackArray4
set_option autoImplicit false
def run (s : State) (words : List U32) : State := words.foldl step s
theorem run_nil (s : State) : run s [] = s := rfl
theorem run_cons (s : State) (w : U32) (ws : List U32) :
    run s (w::ws) = run (step s w) ws := rfl
theorem run_append (s : State) (xs ys : List U32) :
    run s (xs++ys) = run (run s xs) ys := by
  exact List.foldl_append
theorem run_four (s : State) (a b c d : U32) :
    run s [a,b,c,d] = step (step (step (step s a) b) c) d := rfl
def packed (s : State) : A4 × A4 := (pack s.a s.b s.e s.f,pack s.c s.d s.g s.h)
#print axioms run
#print axioms run_nil
#print axioms run_cons
#print axioms run_append
#print axioms run_four
#print axioms packed
end R1Z.PV_CBL_FallbackRoundsModel

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackStateShift
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackStateShift
open PV_CBL_FallbackScalar
set_option autoImplicit false
theorem two_c (s : State) (w0 w1 : U32) : (step (step s w0) w1).c=s.a := rfl
theorem two_d (s : State) (w0 w1 : U32) : (step (step s w0) w1).d=s.b := rfl
theorem two_g (s : State) (w0 w1 : U32) : (step (step s w0) w1).g=s.e := rfl
theorem two_h (s : State) (w0 w1 : U32) : (step (step s w0) w1).h=s.f := rfl
#print axioms two_c
#print axioms two_d
#print axioms two_g
#print axioms two_h
end R1Z.PV_CBL_FallbackStateShift

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackFourModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourModel
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
/-- Factoring of the exact straight-line rounds4 macro; no replaced compressor. -/
def source (abef cdgh w k : A4) : Result (A4×A4) := do
  let t ← PV_CBL_FallbackBlock.sha_fallback_reference.add w k
  let c ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh abef t
  let u ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t
  let a ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef c u
  ok (a,c)
def run4 (s : State) (w0 w1 w2 w3 k0 k1 k2 k3 : U32) : State :=
  run s [U32.wrapping_add w0 k0,U32.wrapping_add w1 k1,
         U32.wrapping_add w2 k2,U32.wrapping_add w3 k3]
#print axioms source
#print axioms run4
end R1Z.PV_CBL_FallbackFourModel

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackFourShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourShape
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
open PV_CBL_FallbackFourModel PV_CBL_FallbackStateShift
set_option autoImplicit false
theorem shape (s : State) (w0 w1 w2 w3 k0 k1 k2 k3 : U32) :
    source (pack s.a s.b s.e s.f) (pack s.c s.d s.g s.h)
      (pack w3 w2 w1 w0) (pack k3 k2 k1 k0) =
    ok (packed (run4 s w0 w1 w2 w3 k0 k1 k2 k3)) := by
  let t0 := U32.wrapping_add w0 k0
  let t1 := U32.wrapping_add w1 k1
  let t2 := U32.wrapping_add w2 k2
  let t3 := U32.wrapping_add w3 k3
  have h1 := PV_CBL_FallbackRoundShape.shape s t0 t1 t3 t2
  have h2 := PV_CBL_FallbackRoundShape.shape (step (step s t0) t1) t2 t3 t1 t0
  simp only [two_c,two_d,two_g,two_h] at h2
  simp only [source,PV_CBL_FallbackBlockLinks.add_eq,PV_CBL_FallbackLaneAdd.shape,
    PV_CBL_FallbackBlockLinks.round_eq,h1,h2,PV_CBL_FallbackBlockSwap.shape,bind_tc_ok]
  simp only [run4,run_four,packed,two_c,two_d,two_g,two_h] <;> rfl
#print axioms shape
end R1Z.PV_CBL_FallbackFourShape

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackFourCanonical
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourCanonical
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
theorem source (s : State) (w0 w1 w2 w3 k0 k1 k2 k3 : U32) :
    PV_CBL_FallbackFourModel.source (pack s.a s.b s.e s.f) (pack s.c s.d s.g s.h)
      (pack w3 w2 w1 w0) (pack k3 k2 k1 k0) =
      let r := PV_CBL_FallbackCanonicalStep.step
        (PV_CBL_FallbackCanonicalStep.step
        (PV_CBL_FallbackCanonicalStep.step
        (PV_CBL_FallbackCanonicalStep.step s (U32.wrapping_add w0 k0)) (U32.wrapping_add w1 k1))
        (U32.wrapping_add w2 k2)) (U32.wrapping_add w3 k3)
      ok (packed r) := by
  simpa only [PV_CBL_FallbackFourModel.run4,run_four,PV_CBL_FallbackCanonicalStep.source] using
    PV_CBL_FallbackFourShape.shape s w0 w1 w2 w3 k0 k1 k2 k3
#print axioms source
end R1Z.PV_CBL_FallbackFourCanonical

end
