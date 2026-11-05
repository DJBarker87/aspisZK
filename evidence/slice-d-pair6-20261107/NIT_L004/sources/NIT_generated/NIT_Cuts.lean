import NIQ_PairComposition
import NIQ_FinishComposition
import NHI_WordEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_Cuts
open Aeneas Aeneas.Std Result AspisR1Stage2 LPi_FieldValues Classical
abbrev E := NE
abbrev K := NQ
abbrev W := FIo_Native.weights.Weights
abbrev Powers := Array E 4#usize
abbrev Parts := Array E 7#usize
abbrev CommonCells := Array K 16#usize
abbrev LowCells := Array E 16#usize
abbrev FE := aspis_core.field.wide_exact.WideExact
abbrev Reply (T : Type) := core.result.Result T verifier.Error
/-- Pointer identities remain opaque addresses; equality of addresses alone is
not asserted to imply equality of model payloads. A reference carries the SAME
chosen decoded payload. Its native association is the retained P6/ABI boundary. -/
structure Ref (T : Type) where
 address : Nat
 value : T

def epick {n : Usize} (xs : Array E n) (i : Nat) : E :=
 xs.val[i]?.getD NHI_Scalar.zero
def kpick {n : Usize} (xs : Array K n) (i : Nat) : K :=
 xs.val[i]?.getD FIo_Native.aspis_core.field.QM31.ZERO
def canonical {n : Usize} (xs : Array E n) : Prop := ∀ x∈xs.val,canonE x
-- These cuts use structural equality for the finite all-limb assertions.
-- to_limbs is the eight raw fields (frozen wide_exact.rs); no normalization.
-- Only the mutable frame actually asserted by the harness is included.

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 181-196.
```rust
 assert!(n==64&&expected==64&&folds==2&&l.calls==2);
 assert!(l.inputs[0].to_limbs()[limb]==alpha[0].to_limbs()[limb]&&l.inputs[1].to_limbs()[limb]==alpha[1].to_limbs()[limb]);
 assert!(ap0[power].to_limbs()[limb]==l.replies[0][power].to_limbs()[limb]&&ap1[power].to_limbs()[limb]==l.replies[1][power].to_limbs()[limb]);
 assert!(parts[slot].to_limbs()[limb]==0);
```
No callee value interpretation is part of this cut. -/
structure Initial where
 inputs : Array E 2#usize
 replies : Fin 2 → Powers
 calls : Nat

def cutInitial (alpha : Array E 2#usize) (l : Initial)
 (ap0 ap1 : Powers) (parts : Parts) : Prop :=
 canonical alpha ∧ (∀ side,canonical (l.replies side)) ∧
 l.calls=2 ∧ l.inputs=alpha ∧ ap0=l.replies 0 ∧ ap1=l.replies 1 ∧
 (∀ slot, slot<7 → epick parts slot=NHI_Scalar.zero)

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 24-37.
```rust
 let good=match g{0=>qw(l.lhs)[limb]==qw(row2[j&3])[limb],1=>qw(l.rhs)[limb]==qw(row3[j>>2])[limb],2=>l.calls==1,_=>qw(cells[k])[limb]==qw(if k==j{l.reply}else{before[k]})[limb]};assert!(good);
```
No callee value interpretation is part of this cut. -/
structure Common where
 lhs : K
 rhs : K
 reply : K
 calls : Nat

def cutCommon (row2 row3 : Array K 4#usize) (j : Nat)
 (before : CommonCells) (l : Common) (after : CommonCells) : Prop :=
 j<16 ∧ l.lhs=kpick row2 (j%4) ∧ l.rhs=kpick row3 (j/4) ∧ l.calls=1 ∧
 ∀ k, k<16 → kpick after k=if k=j then l.reply else kpick before k

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 46-63.
```rust
 let good=match g{0=>l.a.to_limbs()[limb]==ap0[PERM[s%4]].to_limbs()[limb],1=>l.b.to_limbs()[limb]==ap1[PERM[s/4]].to_limbs()[limb],2=>l.count==3&&l.tags==[0,1,2],3=>l.base_a==QUARTER&&l.base_b==QUARTER&&l.scale_b==M31(134217728),4=>l.scale_a.to_limbs()[limb]==l.product.to_limbs()[limb],_=>cells[k].to_limbs()[limb]==if k==s{l.scaled}else{before[k]}.to_limbs()[limb]};assert!(good);
```
No callee value interpretation is part of this cut. -/
structure Low where
 a : E
 b : E
 product : E
 scale_a : E
 scaled : E
 scale_b : U32
 base_a : U32
 base_b : U32
 tags : List Nat
 count : Nat

def perm (i : Nat) : Nat := match i with | 0=>0 | 1=>3 | 2=>2 | _=>1

def cutLow (ap0 ap1 : Powers) (s : Nat) (before : LowCells)
 (l : Low) (after : LowCells) : Prop :=
 s<16 ∧ canonical ap0 ∧ canonical ap1 ∧ canonical before ∧
 canonE l.product ∧ canonE l.scaled ∧
 l.a=epick ap0 (perm (s%4)) ∧ l.b=epick ap1 (perm (s/4)) ∧
 l.count=3 ∧ l.tags=[0,1,2] ∧ l.base_a=536870912#u32 ∧
 l.base_b=536870912#u32 ∧ l.scale_b=134217728#u32 ∧ l.scale_a=l.product ∧
 ∀ k,k<16 → epick after k=if k=s then l.scaled else epick before k

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 71-84.
```rust
 let good=match g{0=>l.mul_a.to_limbs()[limb]==powers[kind].to_limbs()[limb],1=>l.mul_b.to_limbs()[limb]==parts[kind].to_limbs()[limb],2=>l.add_a.to_limbs()[limb]==before.to_limbs()[limb],3=>l.add_b.to_limbs()[limb]==l.product.to_limbs()[limb],4=>l.count==2&&l.tags==[0,1],_=>sum.to_limbs()[limb]==l.reply.to_limbs()[limb]};assert!(good);
```
No callee value interpretation is part of this cut. -/
structure Final where
 mul_a : E
 mul_b : E
 product : E
 add_a : E
 add_b : E
 reply : E
 count : Nat
 tags : List Nat

def cutFinal (parts powers : Parts) (kind : Nat) (before : E)
 (l : Final) (after : E) : Prop :=
 kind<7 ∧ canonical parts ∧ canonical powers ∧ canonE before ∧
 canonE l.product ∧ canonE l.reply ∧
 l.mul_a=epick powers kind ∧ l.mul_b=epick parts kind ∧
 l.add_a=before ∧ l.add_b=l.product ∧ l.count=2 ∧ l.tags=[0,1] ∧ after=l.reply

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 92-105.
```rust
 let good=match g{0=>l.ptr==f.as_ptr()&&l.len==2048&&l.index==j&&l.count==3&&l.tags==[0,1,2],1=>l.mul_a.to_limbs()[limb]==l.coefficient.to_limbs()[limb],2=>l.mul_b.to_limbs()[limb]==libra[j].to_limbs()[limb],3=>l.add_a.to_limbs()[limb]==before[4].to_limbs()[limb],4=>l.add_b.to_limbs()[limb]==l.product.to_limbs()[limb],_=>parts[k].to_limbs()[limb]==if k==4{l.reply}else{before[k]}.to_limbs()[limb]};assert!(good);
```
No callee value interpretation is part of this cut. -/
structure LibraLog where
 ptr : Nat
 len : Nat
 index : Nat
 coefficient : E
 mul_a : E
 mul_b : E
 product : E
 add_a : E
 add_b : E
 reply : E
 count : Nat
 tags : List Nat

def cutLibraLog (f : Ref (Slice U8)) (libra : Powers) (j : Nat)
 (before : Parts) (l : LibraLog) (after : Parts) : Prop :=
 j<4 ∧ f.value.val.length=2048 ∧ canonical libra ∧ canonical before ∧
 canonE l.coefficient ∧ canonE l.product ∧ canonE l.reply ∧
 l.ptr=f.address ∧ l.len=2048 ∧ l.index=j ∧ l.count=3 ∧ l.tags=[0,1,2] ∧
 l.mul_a=l.coefficient ∧ l.mul_b=epick libra j ∧ l.add_a=epick before 4 ∧
 l.add_b=l.product ∧
 ∀ k,k<7 → epick after k=if k=4 then l.reply else epick before k

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 161-179.
```rust
 assert!(l.regular_arg==shared);assert!(out.map_err(error_code)==expected);assert!(l.count==count);
 assert!(l.events[0]==0);if shared&&l.regular.is_ok(){assert!(l.events[1]==1&&l.events[2]==2);if l.partial.is_ok(){assert!(l.events[3]==3);}}
 if out.is_ok(){assert!(l.events[count-1]==4);}
```
No callee value interpretation is part of this cut. -/
structure SameGuard where
 regular_arg : Bool
 regular : Reply Unit
 «partial» : Reply Unit
 high : Reply Unit
 events : Nat → Nat
 count : Nat

def sameExpected (shared : Bool) (l : SameGuard) : Reply Unit × Nat :=
 match l.regular with
 | .Err e => (.Err e,1)
 | .Ok _ => if !shared then (.Ok (),2) else
   match l.«partial» with
   | .Err e => (.Err e,3)
   | .Ok _ => match l.high with
     | .Err e => (.Err e,4)
     | .Ok _ => (.Ok (),5)

def cutSameGuard (shared : Bool) (l : SameGuard) (out : Reply Unit) : Prop :=
 l.regular_arg=shared ∧ out=(sameExpected shared l).1 ∧
 l.count=(sameExpected shared l).2 ∧ l.events 0=0 ∧
 (shared=true → l.regular=.Ok () → l.events 1=1 ∧ l.events 2=2 ∧
   (l.«partial»=.Ok () → l.events 3=3)) ∧
 (out=.Ok () → l.events (l.count-1)=4)

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 199-219.
```rust
 assert!(l.who==&w as *const Weights&&l.shared==shared&&l.folds==2&&l.n==64&&l.alpha==alpha.as_ptr()&&l.alpha_len==2&&l.message==f.as_ptr()&&l.message_len==2048&&l.scratch==scratch.as_ptr()&&l.scratch_len==64&&l.parts==parts.as_ptr());
 assert!(l.p0.to_limbs()[limb]==ap0[power].to_limbs()[limb]&&l.p1.to_limbs()[limb]==ap1[power].to_limbs()[limb]);
 if shared{assert!(l.common==common.as_ptr()&&qw(l.common_value)[limb&3]==qw(common[i])[limb&3]&&l.partial_message==f.as_ptr()&&l.partial_message_len==2048&&l.high_who==&w as *const Weights&&l.high_parts==parts.as_ptr());assert!(l.high_partial.to_limbs()[limb]==l.partial_reply[power].to_limbs()[limb]&&l.high_p0.to_limbs()[limb]==ap0[power].to_limbs()[limb]&&l.high_p1.to_limbs()[limb]==ap1[power].to_limbs()[limb]);}
```
No callee value interpretation is part of this cut. -/
structure PairEdges where
 who : Nat
 alpha : Nat
 message : Nat
 scratch : Nat
 parts : Nat
 common : Nat
 partial_message : Nat
 high_who : Nat
 high_parts : Nat
 shared : Bool
 folds : Nat
 n : Nat
 alpha_len : Nat
 message_len : Nat
 scratch_len : Nat
 partial_message_len : Nat
 p0 : E
 p1 : E
 high_partial : E
 high_p0 : E
 high_p1 : E
 common_value : K
 regular_post : Parts
 partial_reply : Powers

/-- No parts/scratch post-state constraint: pair_argument_edges asserts none. -/
def cutPairEdges (w : Ref W) (alpha : Ref (Array E 2#usize))
 (f : Ref (Slice U8)) (scratch : Ref (Array K 64#usize)) (parts : Ref Parts)
 (ap0 ap1 : Powers) (common : Ref CommonCells) (shared : Bool)
 (power i : Nat) (l : PairEdges) : Prop :=
 w.value.variant=FIo_Native.transport.Variant.S2 ∧
 power<4 ∧ i<16 ∧ canonical alpha.value ∧ canonical ap0 ∧ canonical ap1 ∧
 canonical parts.value ∧ canonical l.regular_post ∧ canonical l.partial_reply ∧
 f.value.val.length=2048 ∧
 l.who=w.address ∧ l.shared=shared ∧ l.folds=2 ∧ l.n=64 ∧
 l.alpha=alpha.address ∧ l.alpha_len=2 ∧ l.message=f.address ∧ l.message_len=2048 ∧
 l.scratch=scratch.address ∧ l.scratch_len=64 ∧ l.parts=parts.address ∧
 l.p0=epick ap0 power ∧ l.p1=epick ap1 power ∧
 (shared=true → l.common=common.address ∧ l.common_value=kpick common.value i ∧
 l.partial_message=f.address ∧ l.partial_message_len=2048 ∧
 l.high_who=w.address ∧ l.high_parts=parts.address ∧
 l.high_partial=epick l.partial_reply power ∧ l.high_p0=epick ap0 power ∧
 l.high_p1=epick ap1 power)

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 225-236.
```rust
 assert!(l.variant==p.variant&&l.alpha==p.semantic_alpha.as_ptr()&&l.z==p.z.as_ptr()&&l.calls==1);
 match out{Ok(w)=>{assert!(error.is_none()&&l.reply.is_none()&&&*w as *const Weights==owner);},Err(e)=>{assert!(Some(error_code(e))==error.map(error_code)&&l.reply.is_some());}}
```
No callee value interpretation is part of this cut. -/
structure NewPort where
 variant : transport.Variant
 alpha : Nat
 z : Nat
 reply : Option (Ref FIo_Install.W)
 error : Option verifier.Error
 calls : Nat

/-- Ownership is represented by an address, without claiming payload equality. -/
def cutNewPort (p : verifier.Prepared) (alpha z owner : Nat)
 (before after : NewPort) (out : Reply (Ref FIo_Install.W)) : Prop :=
 p.variant=transport.Variant.S2 ∧ before.calls=0 ∧
 before.reply.isSome=true ∧ after.variant=p.variant ∧ after.alpha=alpha ∧
 after.z=z ∧ after.calls=1 ∧
 match out with
 | .Ok w => before.error=none ∧ after.reply=none ∧ w.address=owner
 | .Err e => before.error=some e ∧ after.reply.isSome=true

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 238-250.
```rust
 assert!(l.who==owner&&l.alpha==p.alpha.as_ptr()&&l.alpha_len==2&&l.message==f.as_ptr()&&l.message_len==2048&&l.kappa.to_limbs()[limb]==p.kappa.to_limbs()[limb]&&l.calls==1);
 assert!(encoded(out)==encoded(reply));assert!(&*weights as *const Weights==owner);
```
No callee value interpretation is part of this cut. -/
structure PairPort where
 who : Nat
 alpha : Nat
 alpha_len : Nat
 message : Nat
 message_len : Nat
 kappa : FE
 reply : Reply FE
 calls : Nat

def cutPairPort (owner alpha message : Nat) (p : verifier.Prepared)
 (l : PairPort) (out : Reply FE) (afterOwner : Nat) : Prop :=
 p.variant=transport.Variant.S2 ∧ l.who=owner ∧ l.alpha=alpha ∧ l.alpha_len=2 ∧ l.message=message ∧
 l.message_len=2048 ∧ l.kappa=p.kappa ∧ l.calls=1 ∧
 NIQ_ResultEncoding.returning out=NIQ_ResultEncoding.returning l.reply ∧
 afterOwner=owner

/-- Reviewed transcription: /Users/dominic/ZK/.worktrees/cx-slice-d-pair6/evidence/slice-d-pair4-20261107/NIG_stages.patch, sha256 907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289, patch lines 253-292.
```rust
 assert!(out.map_err(error_code)==expected&&l.count==count&&usize::from(l.events[event])==event);
 assert!(l.round_ptr[0]==v.round0.as_ptr()&&l.round_len[0]==224&&l.round_alpha[0].to_limbs()[limb]==p.alpha[0].to_limbs()[limb]&&l.round_claim[0].to_limbs()[limb]==p.claim.to_limbs()[limb]);
 if count>=2{let claim=l.round_reply[0].unwrap();assert!(l.round_ptr[1]==v.round1.as_ptr()&&l.round_len[1]==224&&l.round_alpha[1].to_limbs()[limb]==p.alpha[1].to_limbs()[limb]&&l.round_claim[1].to_limbs()[limb]==claim.to_limbs()[limb]);}
 if count>=3{assert!(l.new.calls==1&&l.new.variant==p.variant&&l.new.alpha==p.semantic_alpha.as_ptr()&&l.new.z==p.z.as_ptr());}
 if count>=4{assert!(l.pair.calls==1&&l.pair.who==owner&&l.pair.alpha==p.alpha.as_ptr()&&l.pair.alpha_len==2&&l.pair.message==v.final_message.as_ptr()&&l.pair.message_len==2048&&l.pair.kappa.to_limbs()[limb]==p.kappa.to_limbs()[limb]);}
 if count>=6{assert!(l.dot_f==v.final_message.as_ptr()&&l.dot_f_len==2048&&l.dot_weights==a.weights.as_ptr()&&l.dot_len==64);}
```
No callee value interpretation is part of this cut. -/
structure FinishLog where
 events : Nat → Nat
 count : Nat
 round_reply : Fin 2 → Reply FE
 round_ptr : Fin 2 → Nat
 round_len : Fin 2 → Nat
 round_alpha : Fin 2 → FE
 round_claim : Fin 2 → FE
 new : NewPort
 pair : PairPort
 dot_reply : Reply FE
 dot_f : Nat
 dot_f_len : Nat
 dot_weights : Nat
 dot_len : Nat

def finishExpected (a : verifier.Accumulator) (l : FinishLog) : Reply Unit × Nat :=
 match l.round_reply 0 with
 | .Err e => (.Err e,1)
 | .Ok _ => match l.round_reply 1 with
   | .Err e => (.Err e,2)
   | .Ok claim => match l.new.error with
     | some e => (.Err e,3)
     | none => match l.pair.reply with
       | .Err e => (.Err e,4)
       | .Ok pair => if pair≠claim then (.Err .Relation,4) else
         match l.dot_reply with
         | .Err e => (.Err e,6)
         | .Ok actual => if a.next≠22#usize ∨ actual≠a.rhs then (.Err .Query,6)
           else (.Ok (),7)

/-- Finish's immutable input records have no writes in the cut; no unasserted
heap/content equality is inferred from the pointer observations. -/
def cutFinishLog (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit) : Prop :=
 p.variant=transport.Variant.S2 ∧ v.round0.val.length=224 ∧ v.round1.val.length=224 ∧
 v.final_message.val.length=2048 ∧ a.weights.val.length=64 ∧
 out=(finishExpected a l).1 ∧ l.count=(finishExpected a l).2 ∧
 (∀ event,event<l.count → l.events event=event) ∧
 l.round_ptr 0=round0 ∧ l.round_len 0=224 ∧
 l.round_alpha 0=NIG_FinishAlpha.alpha p 0 (by decide) ∧ l.round_claim 0=p.claim ∧
 (2≤l.count → l.round_ptr 1=round1 ∧ l.round_len 1=224 ∧
   l.round_alpha 1=NIG_FinishAlpha.alpha p 1 (by decide) ∧ l.round_reply 0=.Ok (l.round_claim 1)) ∧
 (3≤l.count → l.new.calls=1 ∧ l.new.variant=p.variant ∧
   l.new.alpha=semanticAlpha ∧ l.new.z=z) ∧
 (4≤l.count → l.pair.calls=1 ∧ l.pair.who=owner ∧ l.pair.alpha=alpha ∧
   l.pair.alpha_len=2 ∧ l.pair.message=message ∧ l.pair.message_len=2048 ∧ l.pair.kappa=p.kappa) ∧
 (6≤l.count → l.dot_f=message ∧ l.dot_f_len=2048 ∧ l.dot_weights=weights ∧ l.dot_len=64)

end AspisR1.NIT_Cuts
