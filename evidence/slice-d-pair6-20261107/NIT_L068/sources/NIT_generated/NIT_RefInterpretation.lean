import NIT_TailCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_RefInterpretation
open Aeneas Aeneas.Std Result NIT_Cuts

/-- Restricted view of one caller-established valid reference at this cut.
This is the native argument interpretation under retained P6/ABI semantics;
it returns no payload for a different pointer. It is not a native fn pointer.
Two arbitrary Ref.value fields are NEVER identified by equal addresses. -/
def decode {T : Type} (view : Ref T) (pointer : Nat) : Option T :=
 if pointer=view.address then some view.value else none

def updated {T : Type} (view : Ref T) (value : T) : Ref T := ⟨view.address,value⟩

theorem at_pointer {T : Type} (view : Ref T) (pointer : Nat) (same : pointer=view.address) :
 decode view pointer=some view.value := by
 simp only [decode,same,ite_true]

theorem decoded {T : Type} (view : Ref T) (pointer : Nat) (value : T)
 (same : pointer=view.address) (read : decode view pointer=some value) : value=view.value := by
 rw [at_pointer view pointer same] at read
 exact (Option.some.inj read).symm

/-- The mutable place keeps its identity while its model payload is replaced by
its CLOSED callee's post-state. This asserts no before/after value equality. -/
theorem after_write {T : Type} (view : Ref T) (pointer : Nat) (value : T)
 (same : pointer=view.address) : decode (updated view value) pointer=some value :=
 at_pointer (updated view value) pointer same

theorem group_arguments (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts after : Parts) (l : NIT_TailCuts.Tail) (libra : Powers)
 (cut : NIT_TailCuts.groupCut w f low ap0 ap1 parts l after libra) :
 decode w l.who=some w.value ∧ decode f l.bytes=some f.value ∧
 decode low l.low=some low.value ∧ decode ap0 l.ap0=some ap0.value ∧
 decode ap1 l.ap1=some ap1.value ∧ l.extra=w.value.extra := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,who,bytes,_,lowPtr,_,p0,p1,extra,_⟩
 exact ⟨at_pointer w _ who,at_pointer f _ bytes,at_pointer low _ lowPtr,
  at_pointer ap0 _ p0,at_pointer ap1 _ p1,extra⟩

theorem libra_argument (f : Ref (Slice U8)) (libra : Powers) (j : Nat)
 (before after : Parts) (l : LibraLog) (cut : cutLibraLog f libra j before l after) :
 decode f l.ptr=some f.value ∧ l.len=2048 ∧ l.index=j := by
 rcases cut with ⟨_,_,_,_,_,_,_,ptr,len,index,_⟩
 exact ⟨at_pointer f _ ptr,len,index⟩

theorem regular_arguments (w : Ref W) (alpha : Ref (Array E 2#usize))
 (f : Ref (Slice U8)) (scratch : Ref (Array K 64#usize)) (parts : Ref Parts)
 (ap0 ap1 : Powers) (common : Ref CommonCells) (shared : Bool)
 (power i : Nat) (l : PairEdges)
 (cut : cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i l) :
 decode w l.who=some w.value ∧ decode alpha l.alpha=some alpha.value ∧
 decode f l.message=some f.value ∧ decode scratch l.scratch=some scratch.value ∧
 decode parts l.parts=some parts.value := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,who,_,_,_,alphaPtr,_,message,_,scratchPtr,_,partsPtr,_⟩
 exact ⟨at_pointer w _ who,at_pointer alpha _ alphaPtr,at_pointer f _ message,
  at_pointer scratch _ scratchPtr,at_pointer parts _ partsPtr⟩

theorem high_arguments (w : Ref W) (alpha : Ref (Array E 2#usize))
 (f : Ref (Slice U8)) (scratch : Ref (Array K 64#usize)) (parts : Ref Parts)
 (ap0 ap1 : Powers) (common : Ref CommonCells) (power i : Nat) (l : PairEdges)
 (cut : cutPairEdges w alpha f scratch parts ap0 ap1 common true power i l)
 (afterRegular : Parts) :
 decode w l.high_who=some w.value ∧
 decode (updated parts afterRegular) l.high_parts=some afterRegular := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,tail⟩
 obtain ⟨_,_,_,_,who,place,_⟩ := tail rfl
 exact ⟨at_pointer w _ who,after_write parts _ afterRegular place⟩

/-- Read the returned owner through the SAME child-return view. No claim that an
arbitrary out.value equals another arbitrary Ref.value is made. -/
theorem new_payload (p : AspisR1Stage2.verifier.Prepared) (alpha z owner : Nat)
 (before after : NewPort) (out : Ref FIo_Install.W)
 (cut : cutNewPort p alpha z owner before after (.Ok out)) :
 ∃ child,before.reply=some child ∧ decode child out.address=some child.value := by
 rcases cut with ⟨_,_,⟨child,reply,childOwner,_⟩,_,_,_,_,_,_,outOwner⟩
 exact ⟨child,reply,at_pointer child _ (outOwner.trans childOwner.symm)⟩

#print axioms at_pointer
#print axioms decoded
#print axioms after_write
#print axioms group_arguments
#print axioms libra_argument
#print axioms regular_arguments
#print axioms high_arguments
#print axioms new_payload
end AspisR1.NIT_RefInterpretation
