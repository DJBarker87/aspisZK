import FGm_UsizeNext
import FIo_PowersCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_PowersStep
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE wide)
open FGm_ArrayValue (decode value)
abbrev State (N : Usize) := Array NE N × NE × Usize

def Inv {N : Usize} (x : NE) (s : State N) : Prop :=
  FIo_ArrayCanon.Holds s.1 ∧ FIo_WideValues.Canon s.2.1 ∧
  decode s.2.1=decode x^s.2.2.val ∧
  ∀ (j : Nat), j < s.2.2.val → value s.1 j=decode x^j

def Post {N : Usize} (x : NE) (a : Array NE N) : Prop :=
  FIo_ArrayCanon.Holds a ∧ ∀ (j : Nat), j < N.val → value a j=decode x^j

def measure {N : Usize} (s : State N) := N.val-s.2.2.val

theorem step {N : Usize} (x : NE) (hx : FIo_WideValues.Canon x)
    (s : State N) (inv : Inv x s) (out : ControlFlow (State N) (Array NE N))
    (run : FIo_Native.weights.powers_loop.body x s.1 s.2.1 s.2.2=ok out) :
    match out with
    | .done a => Post x a
    | .cont t => Inv x t ∧ measure t<measure s := by
  rcases s with ⟨a,p,i⟩
  rcases inv with ⟨ha,hp,hpower,hvalues⟩
  dsimp only at ha hp hpower hvalues
  unfold FIo_Native.weights.powers_loop.body at run
  split at run
  · rename_i more
    obtain ⟨⟨old,back⟩,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    have updated := FIo_ArrayBack.canonical a i old back hb ha p hp
    have inc := FGm_UsizeNext.val i N more
    have values : ∀ (j : Nat), j < i.val+1 → value (back p) j=decode x^j := by
      intro j hj
      rw [FGm_ArrayUpdate.back_value a i old back hb p j]
      split
      · rename_i same
        simpa only [same] using hpower
      · rename_i other
        exact hvalues j (by omega)
    split at run
    · rename_i last
      have same : done (back p)=out := Result.ok.inj run
      subst out
      refine ⟨updated,?_⟩
      intro j hj
      apply values
      have eqv := congrArg UScalar.val last
      rw [inc] at eqv
      omega
    · obtain ⟨next,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      have same : cont (back p,next,Usize.wrapping_add i 1#usize)=out := Result.ok.inj run
      subst out
      have mulLaw := FIo_WideMulValues.mul p x next hp hx hn
      refine ⟨⟨updated,mulLaw.1,?_,?_⟩,?_⟩
      · change AspisR1CurrentWide.Proof.decodeWide (wide next)=decode x^(Usize.wrapping_add i 1#usize).val
        change AspisR1CurrentWide.Proof.decodeWide (wide p)=decode x^i.val at hpower
        rw [mulLaw.2,hpower,inc,pow_succ]
      · dsimp only
        rw [inc]
        exact values
      · simp only [measure,inc]
        have : i.val < N.val := by scalar_tac
        omega
  · rename_i stop
    have same : done a=out := Result.ok.inj run
    subst out
    refine ⟨ha,?_⟩
    intro j hj
    apply hvalues
    have : N.val ≤ i.val := by scalar_tac
    omega

#print axioms step
end AspisR1.FGm_PowersStep
end
