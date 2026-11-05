import NHM_GroupCoefficient
set_option autoImplicit false
namespace NHM_GroupWeight
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Iter := NHI_RangeProgress.Range
abbrev State := Iter × NE

theorem bind_if {A B : Type} (c : Prop) [Decidable c] (yes no : Result A) (k : A→Result B) :
 ((if c then yes else no) >>= k)=(if c then yes >>= k else no >>= k) := by
 split_ifs <;> rfl

def window (low : Array NE 16#usize) (group bit : Usize) (weight : NE) : Result NE := do
 let challenge ← Array.index_usize low bit
 let mask ← Array.index_usize FIo_Native.weights.S2_INACTIVE_MASKS group
 let shifted ← (1#u16 <<< bit)
 let bits := mask &&& shifted
 if bits != 0#u16 then FIo_Native.aspis_core.field.wide_exact.WideExact.add weight challenge
 else ok weight

def body (low : Array NE 16#usize) (group : Usize) (s : State) : Result (ControlFlow State NE) := do
 let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done s.2)
 | some bit=>do let value ← window low group bit s.2;ok (.cont (next,value))

theorem step (low : Array NE 16#usize) (group : Usize) (s : State) :
 FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2=body low group s := by
 unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body body window
 simp only [lift,bind_assoc_eq,bind_tc_ok,bind_if]
 rfl

theorem canonical (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (group bit : Usize) (before out : NE) (hb : canonE before)
 (run : window low group bit before=ok out) : canonE out := by
 unfold window at run
 obtain ⟨challenge,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨mask,hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨shifted,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 dsimp only at run
 split at run
 · have cc:=NHM_ArrayCanon.read canonE low bit challenge hl hc
   obtain ⟨out',ho,co⟩ := NGW_PolynomialAdd.total before challenge hb cc
   have equal : out'=out := Result.ok.inj (ho.symm.trans run)
   subst out'
   exact co
 · cases Result.ok.inj run
   exact hb

theorem progress (low : Array NE 16#usize) (group : Usize) (s t : State)
 (run : body low group s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact (NHI_RangeProgress.some_next s.1 next j hn).2

theorem decreases (low : Array NE 16#usize) (group : Usize) (s t : State)
 (run : body low group s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,more⟩ := progress low group s t run
 have hv:=congrArg (fun x : Usize=>x.val) last
 omega

def reference (low : Array NE 16#usize) (group : Usize) (weight : NE) :=
 NHI_CountedLoop.unroll (body low group) 17 ({start:=0#usize,«end»:=16#usize},weight)

theorem source (low : Array NE 16#usize) (group : Usize) (weight : NE) :
 FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0
  {start:=0#usize,«end»:=16#usize} low group weight=reference low group weight := by
 unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0 reference
 have same : (fun s : State=>FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2)=body low group := funext (step low group)
 rw [same]
 exact NHI_CountedLoop.agrees (body low group) (fun s=>s.1.end.val-s.1.start.val)
  (decreases low group) 17 _ (by change (16:Nat)-0<17;omega)

#print axioms bind_if
#print axioms step
#print axioms canonical
#print axioms progress
#print axioms decreases
#print axioms source
end NHM_GroupWeight
