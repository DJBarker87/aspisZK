import NJG_RoundDomains
import NJG_RowPrefixes
set_option autoImplicit false
namespace AspisR1.NJG_NativeCuts
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames

def word (q : Q) (i : Fin 4) : U32 := match i.val with
 | 0=>q.c0.a | 1=>q.c0.b | 2=>q.c1.a | _=>q.c1.b

theorem word_ext (a b : Q) (windows : ∀ i,word a i=word b i) : a=b := by
 have h0:=windows 0;have h1:=windows 1;have h2:=windows 2;have h3:=windows 3
 cases a with | mk a0 a1=>
  cases b with | mk b0 b1=>
   cases a0;cases a1;cases b0;cases b1
   simp only [word] at h0 h1 h2 h3
   cases h0;cases h1;cases h2;cases h3;rfl

structure ClaimsPre where
 pointer : Nat
 framed : Slice U8
 p : Fin 3
 reply : core.result.Result (Array Q 29#usize) r1_wire.Error
 count : Nat
 frame : Nat
 priorRow : Fin 3
 priorColumn : Fin 29
 prefixWord : U32
structure ClaimsLog where
 row : U8
 pointer : Nat
 len : Nat
 offset : Nat
 count : Nat
 frame : Nat

def claimsDomain (s : ClaimsPre) : Prop := s.framed.val.length≤3717 ∧ s.count<255 ∧ (0<s.p.val → s.priorRow.val<s.p.val) ∧
 match s.reply with
 | .Ok _=>True
 | .Err (.Length row)=>row=25#u8
 | .Err (.NonCanonical row value)=>row=25#u8 ∧ value.val<29
 | _=>False

/-- Reviewed transcription of NJG_claims_loop::check(args), corrected K020/K021.
Exact assertion SHA and quote are retained in NJG_CERTIFICATES.md. Same borrowed
pointer, row25, len, offset=p*29, incremented call count, unchanged local frame.
No decoder payload or successful-output equation is introduced here. -/
def claimsArgs (s : ClaimsPre) (p : ClaimsLog) : Prop := claimsDomain s ∧
 p.row=25#u8 ∧ p.pointer=s.pointer ∧ p.len=s.framed.val.length ∧ p.offset=s.p.val*29 ∧
 p.count=s.count+1 ∧ p.frame=s.frame

/-- Exact result-window assertions corrected K022/K023: complete Rust rejection fields,
selected copied word on Ok; only the already initialized prior-row word
is observed on either arm. No current-row observation exists on Err. -/
def claimsResult (s : ClaimsPre) (k : Fin 29) (limb : Fin 4)
 (post : core.result.Result Unit r1_wire.Error) (afterWord priorWord : U32) : Prop :=
 claimsDomain s ∧ (0<s.p.val → priorWord=s.prefixWord) ∧ match s.reply with
 | .Ok row=>post=.Ok () ∧ afterWord=word (cell row k) limb
 | .Err error=>post=.Err error

structure RoundsPre where
 prefixToken : Nat
 round : Fin 10
 alpha : Alpha
 running : Q
 state : Block
 next : U8
 reply : RoundOutput
 count : Nat
 frame : Nat
structure RoundsLog where
 prefixToken : Nat
 round : Nat
 alphaWord : U32
 runningWord : U32
 stateByte : U8
 next : U8
 count : Nat
 frame : Nat

/-- One arbitrary source unrolled call site, exact args configuration of
NJG_rounds_driver.rs.txt. Prefix is the same erased shared-borrow token used by
NIX; no payload, aliasing or source invocation is inferred from its numeric value. -/
def roundsArgs (s : RoundsPre) (k : Fin 10) (z : Fin 32) (limb : Fin 4) (p : RoundsLog) : Prop :=
 s.count<255 ∧ p.prefixToken=s.prefixToken ∧ p.round=s.round.val ∧
 p.alphaWord=word (cell s.alpha k) limb ∧ p.runningWord=word s.running limb ∧
 p.stateByte=cell s.state z ∧ p.next=s.next ∧ p.count=s.count+1 ∧ p.frame=s.frame

/-- Returning/error window of the SAME child reply at one unrolled call site;
all eleven deployed WireError variants and their fields are retained. -/
def roundsResult (s : RoundsPre) (k : Fin 10) (z : Fin 32) (limb : Fin 4)
 (post : RoundOutput) (frame : Nat) : Prop := s.count<255 ∧ frame=s.frame ∧
 match s.reply,post with
 | .Err error,.Err out=>out=error
 | .Ok (running,alpha,state,next),.Ok (r,a,t,n)=>
    word r limb=word running limb ∧ word (cell a k) limb=word (cell alpha k) limb ∧
    cell t z=cell state z ∧ n=next
 | _,_=>False

#print axioms word_ext
end AspisR1.NJG_NativeCuts
