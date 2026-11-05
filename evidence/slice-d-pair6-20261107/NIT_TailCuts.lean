import NIT_Cuts
import NIT_LowInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_TailCuts
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts
abbrev R := core.result.Result E FIo_Native.verifier.Error
structure Tail where
 who : Nat
 bytes : Nat
 len : Nat
 low : Nat
 low_len : Nat
 ap0 : Nat
 ap1 : Nat
 extra : Array K 2#usize
 group_reply : E
 libra_reply : Powers
 events : List Nat
 count : Nat

/-- Reviewed transcription: evidence/slice-d-pair6-20261107/NIT_tail.rs.txt, sha256 764bd72c34a30ea68fe30242269d9979d5469026a96d69d161005216aab049a7.
Native assertions:
```rust
 assert!(l.who==&w as *const Weights&&l.bytes==f.as_ptr()&&l.len==2048&&l.low==low.as_ptr()&&l.low_len==16);
 assert!(l.ap0==ap0.as_ptr()&&l.ap1==ap1.as_ptr()&&qw(l.extra[side&1])[limb&3]==qw(w.extra[side&1])[limb&3]&&l.count==2&&l.events==[0,1]);
 assert!(parts[slot].to_limbs()[limb]==if slot==0{l.group_reply}else{before[slot]}.to_limbs()[limb]);
 assert!(libra[side].to_limbs()[limb]==l.libra_reply[side].to_limbs()[limb]);
 assert!(out.map(|x|x.to_limbs()).map_err(|_|())==Ok(sum.to_limbs()));
```
The two source fragments are separated by the already certified loops; this
cut does not claim those loops run or that the complete pair succeeds. -/
def groupCut (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (before : Parts) (l : Tail) (after : Parts)
 (libra : Powers) : Prop :=
 w.value.variant=FIo_Native.transport.Variant.S2 ∧ f.value.val.length=2048 ∧
 canonical low.value ∧ canonical ap0.value ∧ canonical ap1.value ∧ canonical before ∧
 canonE l.group_reply ∧ canonical l.libra_reply ∧
 l.who=w.address ∧ l.bytes=f.address ∧ l.len=2048 ∧ l.low=low.address ∧ l.low_len=16 ∧
 l.ap0=ap0.address ∧ l.ap1=ap1.address ∧ l.extra=w.value.extra ∧ l.count=2 ∧ l.events=[0,1] ∧
 (∀ k,k<7 → epick after k=if k=0 then l.group_reply else epick before k) ∧
 libra=l.libra_reply

def returnCut (sum : E) (out : R) : Prop := canonE sum ∧ out=.Ok sum

def cut (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (before : Parts) (l : Tail) (after : Parts)
 (libra : Powers) (sum : E) (out : R) : Prop :=
 groupCut w f low ap0 ap1 before l after libra ∧ returnCut sum out

/-- Exact assignment/frame extracted from the gap observation. -/
theorem group_frame (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (before : Parts) (l : Tail) (after : Parts)
 (libra : Powers) (h : groupCut w f low ap0 ap1 before l after libra) :
 after=NIT_ArrayFrames.put before 0 l.group_reply := by
 rcases h with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,frame,_⟩
 exact NIT_ArrayFrames.update NHI_Scalar.zero before after 0 l.group_reply (by decide) frame

theorem frame (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (before : Parts) (l : Tail) (after : Parts)
 (libra : Powers) (sum : E) (out : R) (h : cut w f low ap0 ap1 before l after libra sum out) :
 after=NIT_ArrayFrames.put before 0 l.group_reply :=
 group_frame w f low ap0 ap1 before l after libra h.1

#print axioms group_frame
#print axioms frame
end AspisR1.NIT_TailCuts
