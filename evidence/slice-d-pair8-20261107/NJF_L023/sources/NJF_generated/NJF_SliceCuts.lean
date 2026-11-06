import NJF_RegularCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_SliceCuts
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

/-- Reviewed native transcription: NJF_boundary.rs.txt SHA256 8cd0dcf8134e36b263a8709f412a4e7eb370c5f1073867af2e30f00a9fba1aa3.
The native proof is selector-independent; these structural array equalities
are the finite all-limb lift of the quoted selected-word assertions:
`qw(scratch[index])[limb&3]==expected_q[limb&3]`
`parts[slot].to_limbs()[limb]==if entered_high{l.high_parts[slot]}else{l.parts[slot]}.to_limbs()[limb]`
No child source equation is a field. Outer abort-only prefixes are the
separate ruling-(an) extension in NJF_RegularCut.G, not a Rust Err arm. -/
structure Replies where
 regular : RU
 scratch : Scratch
 parts : Parts
 common : CommonCells
 partialReply : RP
 high : RU
 highParts : Parts

/-- Pure native oracle evaluator on its complete Rust Result carriers. The
callee laws select replies; they are not clauses of a root hypothesis. -/
def expected (shared : Bool) (l : Replies) : RU :=
 match l.regular with
 | .Err err => .Err err
 | .Ok _ => if shared then
   match l.partialReply with
   | .Err err => .Err err
   | .Ok _ => l.high
  else .Ok ()

def enteredPartial (shared : Bool) (l : Replies) : Prop := l.regular=.Ok () ∧ shared=true
def enteredHigh (shared : Bool) (l : Replies) : Prop :=
 enteredPartial shared l ∧ ∃ values,l.partialReply=.Ok values

def count (shared : Bool) (l : Replies) : Nat :=
 if ¬enteredPartial shared l then 1 else if ¬enteredHigh shared l then 3 else 4

structure Arguments where
 regularOwner : Nat
 regularAlpha : Nat
 regularMessage : Nat
 regularScratch : Nat
 regularParts : Nat
 regularShared : Bool
 regularAlphaLength : Nat
 regularMessageLength : Nat
 folds : Nat
 n : Nat
 ap0 : Powers
 ap1 : Powers
 commonOwner : Nat
 partialMessage : Nat
 partialMessageLength : Nat
 partialCommon : CommonCells
 highOwner : Nat
 highParts : Nat
 highAP0 : Powers
 highAP1 : Powers
 highBefore : Parts
 highPartial : Powers

/-- Exactly the regular/shared windows, full mutation results, and chronological
prefix asserted natively. Immutable reference payloads are the SAME decoded
caller values; no equality of arbitrary equal-address payloads is inferred. -/
def cut (c : Context) (shared : Bool) (l : Replies) (args : Arguments)
 (scratch : Scratch) (parts : Parts) (out : RU) (events : Nat → Nat) (calls : Nat) : Prop :=
 canonical l.parts ∧ canonical l.highParts ∧
 (∀ values,l.partialReply=.Ok values → canonical values) ∧
 (alloc.vec.Vec.deref l.scratch).val.length=64 ∧
 args.regularOwner=c.w.address ∧ args.regularAlpha=c.alpha.address ∧
 args.regularMessage=c.f.address ∧ args.regularScratch=c.scratchAddress ∧
 args.regularParts=c.partsAddress ∧ args.regularShared=shared ∧
 args.regularAlphaLength=2 ∧ args.regularMessageLength=2048 ∧ args.folds=2 ∧ args.n=64 ∧
 args.ap0=c.ap0.value ∧ args.ap1=c.ap1.value ∧
 out=expected shared l ∧ calls=count shared l ∧ events 0=0 ∧
 scratch=l.scratch ∧ parts=(if enteredHigh shared l then l.highParts else l.parts) ∧
 (enteredPartial shared l → events 1=1 ∧ events 2=2 ∧ args.commonOwner=c.w.address ∧
  args.partialMessage=c.f.address ∧ args.partialMessageLength=2048 ∧ args.partialCommon=l.common) ∧
 (enteredHigh shared l → events 3=3 ∧ args.highOwner=c.w.address ∧ args.highParts=c.partsAddress ∧
  args.highAP0=c.ap0.value ∧ args.highAP1=c.ap1.value ∧ args.highBefore=l.parts ∧
  ∀ values,l.partialReply=.Ok values → args.highPartial=values)

def log (w : W) (l : Replies) : NJF_RegularCut.Log :=
 ⟨ok (l.regular,l.scratch,l.parts),ok (w,l.common),ok l.partialReply,ok (l.high,l.highParts)⟩

/-- The complete returning G agrees with the exact Rust Result/state evaluator.
This covers shared success and all eight returning errors without a successful
child hypothesis. The full Parts post is retained on high Err. -/
theorem evaluator (w : W) (shared : Bool) (l : Replies) :
 NJF_RegularCut.G shared (log w l)=
 (ok (expected shared l,l.scratch,if enteredHigh shared l then l.highParts else l.parts),
  if ¬enteredPartial shared l then [0] else if ¬enteredHigh shared l then [0,1,2] else [0,1,2,3]) := by
 cases hr : l.regular with
 | Err err => simp [NJF_RegularCut.G,log,expected,enteredPartial,enteredHigh,hr]
 | Ok unit =>
  cases unit
  cases shared with
  | false => simp [NJF_RegularCut.G,log,expected,enteredPartial,enteredHigh,hr]
  | true =>
   cases hp : l.partialReply with
   | Err err => simp [NJF_RegularCut.G,log,expected,enteredPartial,enteredHigh,hr,hp]
   | Ok values => simp [NJF_RegularCut.G,log,expected,enteredPartial,enteredHigh,hr,hp]

#print cut
#print axioms evaluator
end AspisR1.NJF_SliceCuts
