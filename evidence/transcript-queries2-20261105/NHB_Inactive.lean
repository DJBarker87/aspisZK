import NHB_Reference
set_option autoImplicit false
namespace AspisR1.NHB_Inactive
open Aeneas Aeneas.Std
abbrev Scan := NGQ_SamplerTrace.State

def cell (a : Array U32 22#usize) (j : Fin 22) : U32 :=
  a.val[j.val]'(by have := a.property; change a.val.length=22 at this; omega)

def State (s : Scan) : Prop := ∀ j : Fin 22,
  s.accepted_len.val≤j.val → cell s.accepted j=0#u32

theorem initial : State NGQ_SamplerPacket.initial := by
  intro j _
  have member : cell NGQ_SamplerPacket.initial.accepted j ∈
      NGQ_SamplerPacket.initial.accepted.val := by
    exact List.getElem_mem _
  change cell NGQ_SamplerPacket.initial.accepted j ∈ List.replicate 22 (0#u32) at member
  exact (List.mem_replicate.mp member).2

/-- Inactive zeros are preserved for ANY membership reply. This domain fact
therefore does not depend on assuming correct native contains semantics. -/
theorem frame_preserves (s next : Scan) (x : U32) (member : Bool)
    (frame : NGQ_SamplerStep.Frame s next x member) (initial : State s) : State next := by
  have len := frame.2.1
  have array := frame.2.2
  intro j after
  cases member with
  | true =>
    simp only [if_true,Nat.add_zero] at len array
    have same : next.accepted=s.accepted := Subtype.ext array
    have before : s.accepted_len.val≤j.val := by omega
    rw [same]
    exact initial j before
  | false =>
    simp only [Bool.false_eq_true,if_false] at len array
    have same : next.accepted=s.accepted.set s.accepted_len x := Subtype.ext array
    have before : s.accepted_len.val≤j.val := by omega
    have different : j.val≠s.accepted_len.val := by omega
    rw [same]
    have window : cell (s.accepted.set s.accepted_len x) j=
        (if j.val=s.accepted_len.val then x else cell s.accepted j) :=
      NHB_Reference.set_window s x j
    rw [window]
    simpa only [different,if_false] using initial j before

theorem word_invariant {cursor last : Nat} {xs : List U32}
    {s final : Scan} {stop : Option Bool}
    (edges : NHB_WordTrace.Trace cursor xs s final last stop)
    (initial : State s) : State final := by
  revert initial
  induction edges with
  | exhausted cursor s => intro initial; exact initial
  | stopped cursor x xs s full => intro initial; exact initial
  | continuing cursor x xs s next final last stop hlen hdraw frame tail ih =>
    intro initial
    exact ih (frame_preserves s next x _ frame initial)

#print axioms initial
#print axioms frame_preserves
#print axioms word_invariant
end AspisR1.NHB_Inactive
