import CuSavingsCanonicalDotsPush
import CuSavingsCanonicalDotsFinish
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsInvariant
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField CuSavingsCanonicalDotsChecked
variable [Shared]
private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

def initial : old_pairing.EbyKDot :=
  ⟨⟨Array.repeat 4#usize 0#u64,0#usize⟩,
   ⟨Array.repeat 4#usize 0#u64,0#usize⟩,0#usize⟩

theorem old_new : old_pairing.EbyKDot.new=.ok initial := rfl

theorem new_new : new_pairing.EbyKDot.new=.ok (project initial) := rfl

theorem initial_counts : RelatedCounts initial := ⟨rfl,rfl⟩

theorem dot_count (self out : old_pairing.canonical.Dot)
    (a b : Array U32 4#usize) (h : old_pairing.canonical.Dot.push self a b=.ok out) :
    (self.count+1#usize : Result Usize)=.ok out.count := by
  unfold old_pairing.canonical.Dot.push at h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨count,hcount,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨sums,_,h⟩ := bind_ok _ _ _ h
  have heq := Result.ok.inj h
  cases heq
  exact hcount

theorem push_counts (self out : old_pairing.EbyKDot)
    (value : field.wide_exact.WideExact) (scalar : field.QM31)
    (hc : WideCanonical value) (hi : RelatedCounts self)
    (h : old_pairing.EbyKDot.push self value scalar=.ok (.Ok (),out)) :
    RelatedCounts out := by
  unfold old_pairing.EbyKDot.push at h
  split at h
  · cases h
  · simp only [field.wide_exact.WideExact.impl.c0,field.wide_exact.WideExact.impl.c1,
      checked_q value.c0 hc.1,checked_q value.c1 hc.2,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    cases hs : old_pairing.checked_q scalar with
    | fail e => rw [hs] at h;cases h
    | div => rw [hs] at h;cases h
    | ok check =>
      rw [hs] at h
      cases check with
      | Err error => cases h
      | Ok word =>
        simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨left,hl,h⟩ := bind_ok _ _ _ h
        obtain ⟨right,hr,h⟩ := bind_ok _ _ _ h
        obtain ⟨count,hcount,h⟩ := bind_ok _ _ _ h
        have heq := Result.ok.inj h
        have hout := congrArg Prod.snd heq
        cases hout
        have hlcount := dot_count self.c0 left (limbs value.c0) word hl
        have hrcount := dot_count self.c1 right (limbs value.c1) word hr
        rw [hi.1,hcount] at hlcount
        rw [hi.2,hcount] at hrcount
        exact ⟨(Result.ok.inj hlcount).symm,(Result.ok.inj hrcount).symm⟩

#print axioms old_new
#print axioms new_new
#print axioms initial_counts
#print axioms dot_count
#print axioms push_counts
end AspisR1.CuSavingsCanonicalDotsInvariant
