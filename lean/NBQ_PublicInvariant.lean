import NBQ_U06
set_option autoImplicit false
namespace NBQ_PublicInvariant
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev State := FIo_Native.fast_pairing.EbyKDot

def Bound (s : Dot) (n : Nat) : Prop :=
  s.sums.val[0]!.val ≤ n*LPf_DotWordStep.bound ∧
  s.sums.val[1]!.val ≤ n*LPf_DotWordStep.bound ∧
  s.sums.val[2]!.val ≤ n*LPf_DotWordStep.bound ∧
  s.sums.val[3]!.val ≤ n*LPf_DotWordStep.bound

def Inv (s : State) : Prop :=
  s.count.val≤4096 ∧ Bound s.c0 s.count.val ∧ Bound s.c1 s.count.val

theorem update (s : Dot) (raw : LPm_PublicState.Raw) (n : Nat)
    (cap : n<4096) (h : Bound s n) : Bound (LPm_PublicState.update s raw) (n+1) := by
  obtain ⟨a,b,c,d,hs⟩ := LPf_ArrayFour.shape s.sums
  obtain ⟨e,f,g,k,hr⟩ := LPf_ArrayFour.shape raw
  have st : s=⟨Array.make 4#usize [a,b,c,d]⟩ := by
    cases s; exact congrArg FIo_Native.fast_pairing.canonical.Dot.mk hs
  subst s
  subst raw
  simp only [Bound,LPm_PublicState.update,Array.make,List.getElem!_cons_zero,
    List.getElem!_cons_succ] at h ⊢
  exact ⟨(LPf_DotWordStep.value a e n cap h.1).2,
    (LPf_DotWordStep.value b f n cap h.2.1).2,
    (LPf_DotWordStep.value c g n cap h.2.2.1).2,
    (LPf_DotWordStep.value d k n cap h.2.2.2).2⟩

theorem initial : ∃ s, FIo_Native.fast_pairing.EbyKDot.new=ok s ∧ Inv s := by
  refine ⟨_,NBQ_U06.new,?_⟩
  simp [Inv,Bound,Array.repeat]

theorem step (s : State) (v : NE) (q : NQ) (h : Inv s)
    (cap : s.count.val<4096) (hv : canonE v) (hq : canonQ q) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),out) ∧
      Inv out ∧ out.count.val=s.count.val+1 := by
  obtain ⟨lo,hi,out,run,_,_,hl,hr,count⟩ := NBQ_U06.push s v q hv hq cap
  refine ⟨out,run,⟨by omega,?_,?_⟩,count⟩
  · rw [hl,count];exact update s.c0 lo s.count.val cap h.2.1
  · rw [hr,count];exact update s.c1 hi s.count.val cap h.2.2
#print axioms update
#print axioms initial
#print axioms step
end NBQ_PublicInvariant
