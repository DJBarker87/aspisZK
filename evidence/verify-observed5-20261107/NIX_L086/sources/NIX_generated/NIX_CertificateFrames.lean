import NIX_ProducerInstall
import NIX_ActiveFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_CertificateFrames
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
attribute [local instance] Classical.propDecidable
abbrev Q := aspis_core.field.QM31
abbrev Block := Array U8 32#usize
abbrev Alpha := Array Q 10#usize
abbrev Polynomial := Array Q 28#usize

def cell {T : Type} {N : Usize} (a : Array T N) (i : Fin N.val) : T := FJb_TailCell.cell a i

/-- Universal observation windows determine the complete fixed-array carrier. -/
theorem array_ext {T : Type} {N : Usize} (a b : Array T N)
 (windows : ∀ i : Fin N.val,cell a i=cell b i) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · rw [a.property,b.property]
 · intro i ha hb
   exact windows ⟨i,by simpa only [a.property] using ha⟩

structure RoundPre where
 prefixToken : Nat
 framed : Slice U8
 round : Usize
 alpha : Alpha
 running : Q
 beforeState : Block
 beforeNext : U8
 polynomial : core.result.Result Polynomial r1_wire.Error
 boundary : Q
 semantic : core.result.Result Q r1_wire.Error
 newState : Block
 newNext : U8
 value : Q
 count : Nat
 frame : Nat
 seed : Q
 oldState : Block
 times : Fin 4 → Nat

structure RoundLog where
 getterPrefix : Fin 2 → Nat
 getterRow : Fin 2 → Nat
 getterCount : Nat
 decodeRow : Nat
 decodePointer : Nat
 decodeLength : Nat
 decodeOffset : Nat
 boundaryValue : Q
 valuePolynomial : Q
 valueAlpha : Q
 valueRound : Nat
 semanticRow : Nat
 semanticPointer : Option Nat
 semanticLength : Nat
 semanticState : Block
 semanticNext : U8
 times : Fin 4 → Nat
 count : Nat
 frame : Nat

def decoded (s : RoundPre) : Bool := match s.polynomial with | .Ok _=>true | .Err _=>false

def sampled (s : RoundPre) : Bool := decoded s && decide (s.boundary=s.running)

def finished (s : RoundPre) : Bool := sampled s && match s.semantic with | .Ok _=>true | .Err _=>false

def polyCell (s : RoundPre) (k : Fin 28) : Q :=
 match s.polynomial with | .Ok p=>cell p k | .Err _=>s.seed

def alphaCell (s : RoundPre) (j : Fin 10) : Q :=
 if j.val=s.round.val then match s.semantic with | .Ok q=>q | .Err _=>s.alpha.val[j.val]'(by simpa only [s.alpha.property] using j.isLt)
 else cell s.alpha j

def domain (s : RoundPre) : Prop :=
 s.round.val<10 ∧ s.framed.val.length≤3717 ∧ s.count<252 ∧
 (match s.polynomial with
 | .Ok _=>True
 | .Err (.Length row)=>row.val=15+s.round.val
 | .Err (.NonCanonical row value)=>row.val=15+s.round.val ∧ value.val<28
 | _=>False) ∧
 (match s.semantic with | .Ok _=>True | .Err (.RowOrder _ _)=>True | _=>False)

/-- Reviewed transcription of NIX_round_local.rs.txt, args configuration,
K073/K074: exact getter token/row and count; decoder row/ptr/len/off; boundary
coefficient observation; semantic same record and pre-state; value polynomial,
alpha and round observations; timestamps and all untouched cache cells/frame.
The source SHA and exact quoted lines are pinned in NIX_CERTIFICATES.md.
Pointer is the same borrowed-frame identity token, not a hash of frame bytes.
No callee value law or successful round is included in this proposition. -/
def roundArgs (s : RoundPre) (pointer : Nat) (k : Fin 28) (j : Fin 10) (z : Fin 32)
 (p : RoundLog) : Prop :=
 domain s ∧ p.getterPrefix 0=s.prefixToken ∧ p.getterRow 0=15+s.round.val ∧
 p.getterCount=(if sampled s then 2 else 1) ∧
 p.getterPrefix 1=(if sampled s then s.prefixToken else 0) ∧
 p.getterRow 1=(if sampled s then 15+s.round.val else 0) ∧
 p.decodeRow=15+s.round.val ∧ p.decodePointer=pointer ∧
 p.decodeLength=s.framed.val.length ∧ p.decodeOffset=0 ∧ p.times 0=s.count ∧ p.frame=s.frame ∧
 p.boundaryValue=polyCell s k ∧ p.times 1=(if decoded s then s.count+1 else s.times 1) ∧
 p.semanticRow=(if sampled s then 15+s.round.val else 0) ∧
 p.semanticPointer=(if sampled s then some pointer else none) ∧
 p.semanticLength=(if sampled s then s.framed.val.length else 0) ∧
 cell p.semanticState z=(if sampled s then cell s.beforeState z else cell s.oldState z) ∧
 p.semanticNext=(if sampled s then s.beforeNext else 0#u8) ∧
 p.times 2=(if sampled s then s.count+2 else s.times 2) ∧
 p.valuePolynomial=(if finished s then polyCell s k else s.seed) ∧
 p.valueAlpha=(if finished s then alphaCell s j else s.seed) ∧
 p.valueRound=(if finished s then s.round.val else 99) ∧
 p.times 3=(if finished s then s.count+3 else s.times 3) ∧
 p.count=s.count+(if !decoded s then 1 else if !decide (s.boundary=s.running) then 2 else
  match s.semantic with | .Err _=>3 | .Ok _=>4)

abbrev RoundOutput := core.result.Result (Q × Alpha × Block × U8) r1_wire.Error

/-- Exact K075/K076 returning/error cut on arbitrary j<10,z<32. The actual
native SolanaDigest is a zero-sized value; the frame observes its state/next
and every Q limb. This states only the asserted windows, not an array equality. -/
def roundResult (s : RoundPre) (j : Fin 10) (z : Fin 32) (post : RoundOutput) : Prop :=
 domain s ∧ match s.polynomial with
 | .Err error=>post=.Err error
 | .Ok _=>if s.boundary≠s.running then post=.Err (.Boundary s.round) else
   match s.semantic with
   | .Err error=>post=.Err error
   | .Ok _=>∃ alpha state,
     post=.Ok (s.value,alpha,state,s.newNext) ∧ cell alpha j=alphaCell s j ∧
     cell state z=cell s.newState z

/-- Error branches retain their complete original error constructor/payload. -/
theorem decode_error (s : RoundPre) (j : Fin 10) (z : Fin 32) (post : RoundOutput)
 (error : r1_wire.Error) (reply : s.polynomial=.Err error)
 (certificate : roundResult s j z post) : post=.Err error := by
 have h:=certificate.2
 simpa only [reply] using h

/-- The producer token needed by both logged getters is obtained before any
round/decoder success premise, from the SAME accepted prefix. -/
theorem same_record (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (row : U8) (bound : row.val<27) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) row=ok (.Ok record) ∧
 record.row=row ∧ record.framed.val.length=NGX_PrefixGeometry.width row.val :=
 NIX_ProducerInstall.framed bytes pre parsed row bound

#print axioms array_ext
#print axioms decode_error
#print axioms same_record
end AspisR1.NIX_CertificateFrames

namespace AspisR1.NIX_RawTag
open Aeneas Aeneas.Std Result
/-- The frozen Copy-tag raw channel bound; only a 62-bit constant, no recurrence. -/
def bound : Nat := 2147483646*2147483646

theorem product_bound (x y : Nat) (hx : x<2147483647) (hy : y<2147483647) :
 x*y≤bound := Nat.mul_le_mul (by omega) (by omega)

theorem four_bound : 4*bound<2^64 := by decide

theorem one_add (raw product n : Nat) (live : n<4) (pre : raw≤n*bound)
 (value : product≤bound) : raw+product≤(n+1)*bound ∧ raw+product<2^64 := by
 have next : (n+1)*bound≤4*bound := Nat.mul_le_mul_right bound (by omega)
 constructor
 · rw [Nat.add_mul,Nat.one_mul];omega
 · have total : raw+product≤(n+1)*bound := by rw [Nat.add_mul,Nat.one_mul];omega
   exact lt_of_le_of_lt (le_trans total next) four_bound

/-- Emitted primitive-u64 multiplication law paired with the opaque product
ports; the native gate never executes the 31-by-31 product. -/
theorem product (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 ∃ out,((UScalar.cast .U64 x : U64)*(UScalar.cast .U64 y : U64) : Result U64)=ok out ∧
 out.val=x.val*y.val ∧ out.val≤bound := by
 have valueBound:=product_bound x.val y.val hx hy
 have machine : x.val*y.val<2^64 := lt_of_le_of_lt valueBound (by have h:=four_bound;unfold bound at *;omega)
 have spec : ((UScalar.cast .U64 x : U64)*(UScalar.cast .U64 y : U64) : Result U64)
  ⦃ out=>out.val=x.val*y.val ⦄ := by
  apply UScalar.mul_spec
  scalar_tac
 obtain ⟨out,run,value⟩:=WP.spec_imp_exists spec
 exact ⟨out,run,value,by rw [value];exact valueBound⟩

#print axioms product_bound
#print axioms four_bound
#print axioms one_add
#print axioms product
end AspisR1.NIX_RawTag
end
