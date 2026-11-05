from pathlib import Path
import hashlib
E=Path(__file__).resolve().parent
P=E.parent/'slice-d-pair4-20261107/NIG_stages.patch'
lines=P.read_text().splitlines(); sha=hashlib.sha256(P.read_bytes()).hexdigest()
s='''import NIQ_PairComposition
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
'''
def add(name,a,b,body):
 global s
 quote='\n'.join(l[1:] for l in lines[a-1:b] if 'assert!'in l or 'let good='in l)
 s+=f'\n/-- Reviewed transcription: {P.as_posix()}, sha256 {sha}, patch lines {a}-{b}.\n```rust\n{quote}\n```\nNo callee value interpretation is part of this cut. -/\n'+body+'\n'
add('Initial',181,196,'''structure Initial where
 inputs : Array E 2#usize
 replies : Fin 2 → Powers
 calls : Nat

def cutInitial (alpha : Array E 2#usize) (l : Initial)
 (ap0 ap1 : Powers) (parts : Parts) : Prop :=
 canonical alpha ∧ (∀ side,canonical (l.replies side)) ∧
 l.calls=2 ∧ l.inputs=alpha ∧ ap0=l.replies 0 ∧ ap1=l.replies 1 ∧
 (∀ slot, slot<7 → epick parts slot=NHI_Scalar.zero)''')
add('Common',24,37,'''structure Common where
 lhs : K
 rhs : K
 reply : K
 calls : Nat

def cutCommon (row2 row3 : Array K 4#usize) (j : Nat)
 (before : CommonCells) (l : Common) (after : CommonCells) : Prop :=
 j<16 ∧ l.lhs=kpick row2 (j%4) ∧ l.rhs=kpick row3 (j/4) ∧ l.calls=1 ∧
 ∀ k, k<16 → kpick after k=if k=j then l.reply else kpick before k''')
add('Low',46,63,'''structure Low where
 a b product scale_a scaled : E
 scale_b base_a base_b : U32
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
 ∀ k,k<16 → epick after k=if k=s then l.scaled else epick before k''')
add('Final',71,84,'''structure Final where
 mul_a mul_b product add_a add_b reply : E
 count : Nat
 tags : List Nat

def cutFinal (parts powers : Parts) (kind : Nat) (before : E)
 (l : Final) (after : E) : Prop :=
 kind<7 ∧ canonical parts ∧ canonical powers ∧ canonE before ∧
 canonE l.product ∧ canonE l.reply ∧
 l.mul_a=epick powers kind ∧ l.mul_b=epick parts kind ∧
 l.add_a=before ∧ l.add_b=l.product ∧ l.count=2 ∧ l.tags=[0,1] ∧ after=l.reply''')
add('LibraLog',92,105,'''structure LibraLog where
 ptr len index : Nat
 coefficient mul_a mul_b product add_a add_b reply : E
 count : Nat
 tags : List Nat

def cutLibraLog (f : Ref (Slice U8)) (libra : Powers) (j : Nat)
 (before : Parts) (l : LibraLog) (after : Parts) : Prop :=
 j<4 ∧ f.value.val.length=2048 ∧ canonical libra ∧ canonical before ∧
 canonE l.coefficient ∧ canonE l.product ∧ canonE l.reply ∧
 l.ptr=f.address ∧ l.len=2048 ∧ l.index=j ∧ l.count=3 ∧ l.tags=[0,1,2] ∧
 l.mul_a=l.coefficient ∧ l.mul_b=epick libra j ∧ l.add_a=epick before 4 ∧
 l.add_b=l.product ∧
 ∀ k,k<7 → epick after k=if k=4 then l.reply else epick before k''')
add('SameGuard',161,179,'''structure SameGuard where
 regular_arg : Bool
 regular partial high : Reply Unit
 events : Nat → Nat
 count : Nat

def sameExpected (shared : Bool) (l : SameGuard) : Reply Unit × Nat :=
 match l.regular with
 | .Err e => (.Err e,1)
 | .Ok _ => if !shared then (.Ok (),2) else
   match l.partial with
   | .Err e => (.Err e,3)
   | .Ok _ => match l.high with
     | .Err e => (.Err e,4)
     | .Ok _ => (.Ok (),5)

def cutSameGuard (shared : Bool) (l : SameGuard) (out : Reply Unit) : Prop :=
 l.regular_arg=shared ∧ out=(sameExpected shared l).1 ∧
 l.count=(sameExpected shared l).2 ∧ l.events 0=0 ∧
 (shared=true → l.regular=.Ok () → l.events 1=1 ∧ l.events 2=2 ∧
   (l.partial=.Ok () → l.events 3=3)) ∧
 (out=.Ok () → l.events (l.count-1)=4)''')
add('PairEdges',199,219,'''structure PairEdges where
 who alpha message scratch parts common partial_message high_who high_parts : Nat
 shared : Bool
 folds n alpha_len message_len scratch_len partial_message_len : Nat
 p0 p1 high_partial high_p0 high_p1 : E
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
 l.high_p1=epick ap1 power)''')
add('NewPort',225,236,'''structure NewPort where
 variant : transport.Variant
 alpha z : Nat
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
 | .Err e => before.error=some e ∧ after.reply.isSome=true''')
add('PairPort',238,250,'''structure PairPort where
 who alpha alpha_len message message_len : Nat
 kappa : FE
 reply : Reply FE
 calls : Nat

def cutPairPort (owner alpha message : Nat) (p : verifier.Prepared)
 (l : PairPort) (out : Reply FE) (afterOwner : Nat) : Prop :=
 p.variant=transport.Variant.S2 ∧ l.who=owner ∧ l.alpha=alpha ∧ l.alpha_len=2 ∧ l.message=message ∧
 l.message_len=2048 ∧ l.kappa=p.kappa ∧ l.calls=1 ∧
 NIQ_ResultEncoding.returning out=NIQ_ResultEncoding.returning l.reply ∧
 afterOwner=owner''')
add('FinishLog',253,292,'''structure FinishLog where
 events : Nat → Nat
 count : Nat
 round_reply : Fin 2 → Reply FE
 round_ptr round_len : Fin 2 → Nat
 round_alpha round_claim : Fin 2 → FE
 new : NewPort
 pair : PairPort
 dot_reply : Reply FE
 dot_f dot_f_len dot_weights dot_len : Nat

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
 (6≤l.count → l.dot_f=message ∧ l.dot_f_len=2048 ∧ l.dot_weights=weights ∧ l.dot_len=64)''')
# Expand grouped structure fields; Lean reads a b : T as a function field.
import re
s=re.sub(r'(?m)^ ([a-zA-Z_][a-zA-Z_0-9]*(?: [a-zA-Z_][a-zA-Z_0-9]*)+) : (.+)$',lambda m:'\n'.join(' '+('«partial»' if n=='partial' else n)+' : '+m[2] for n in m[1].split()),s)
s=re.sub(r'l\.partial\b', 'l.«partial»', s)
# Preserve verbatim Rust assertion quotations.
for m in list(re.finditer(r'```rust\n(.*?)\n```',s,re.S))[::-1]:
 s=s[:m.start(1)]+m[1].replace('l.«partial»','l.partial')+s[m.end(1):]
s+='\nend AspisR1.NIT_Cuts\n' 
(E/'NIT_Cuts.lean').write_text(s)
