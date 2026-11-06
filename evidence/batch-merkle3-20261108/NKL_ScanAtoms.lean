import NKL_ScanDomains
set_option autoImplicit false
noncomputable section
namespace NKL_ScanAtoms
open Aeneas Aeneas.Std Result AspisR1 NKL_Checks
abbrev Reply := NKB_CanonicalRange.ScanResult

def kReply (bytes : Slice U8) : Result Reply := do
 let r←NKL_CanonicalKCarrier.mapResult (Option.map NKL_ClosedChildren.qToCaller)
  (NET_ParserComposed.quadratic bytes)
 ok (NKB_CanonicalOpening.reply r.isSome)

/-- Actual CLOSED child bodies, at the original context's selected arguments.
No oracle outcome is a free parameter. Off-domain scalar None is explicit. -/
def child : Check→Result Reply
 | .cv proof => do
   let r←NFU_Retarget.compact.check_values (NKB_CanonicalPrefix.values proof)
   ok (NKL_CanonicalChildren.convert r)
 | .ec site => do
   let r←NFU_Retarget.verifier.echeck site.bytes false
   ok (match r with | .Ok u=>.Ok u | .Err _=>.Err .Parse)
 | .view proof i => do
   let _←NEO_TailRef.opening proof i
   ok (.Ok ())
 | .scalar q s l => match NKB_CanonicalScalarLoop.read q s l with
   | none=>ok (.Err .Parse)
   | some b=>do
     let r←S8OwnedP6.aspis_core.field.M31.from_le_bytes b
     ok (NKB_CanonicalOpening.reply r.isSome)
 | .c1 q s => kReply (NKB_CanonicalTail.window q s)
 | .c2 q s l => kReply (NKB_CanonicalRange.window q s l)
 | .invalid => fail .panic

theorem k (bytes : Slice U8) (width:bytes.val.length=16) :
 kReply bytes=ok (NKB_CanonicalOpening.reply (NKL_CanonicalKCarrier.selected bytes).isSome) := by
 unfold kReply
 rw [NKL_ClosedChildren.quadratic bytes width]
 rfl

/-- Universal child installation, including rejection, with every domain
proved separately from the parent's original proof width. -/
theorem source (c : Check) (domain:NKL_ScanDomains.Domain c) :
 child c=ok (NKB_CanonicalOpening.reply (test c)) := by
 cases c with
 | cv proof=>exact NKL_CanonicalChildren.compact_call _
 | ec site=>exact NKL_CanonicalChildren.echeck_call _
 | view proof i=>
   obtain ⟨q,read,_,_⟩:=NKL_ClosedChildren.opening proof domain.1 i domain.2
   simp only [child,NKL_ClosedChildren.opening_reference,read,bind_tc_ok,test]
   rfl
 | scalar q s l=>
   cases read:NKB_CanonicalScalarLoop.read q s l with
   | none=>simp only [child,test,read,Option.bind_none,Option.isSome_none];rfl
   | some b=>simp only [child,test,read,Option.bind_some];rw [NKL_ClosedChildren.scalar];rfl
 | c1 q s=>exact k _ (NKB_CanonicalDomains.c1 q domain.1 s domain.2)
 | c2 q s l=>exact k _ (NKB_CanonicalDomains.c2 q domain.1 s l domain.2.1 domain.2.2)
 | invalid=>exact False.elim domain

def accepted (c : Check) : Bool :=
 match child c with | .ok (.Ok _)=>true | _=>false

theorem accepted_test (c : Check) (domain:NKL_ScanDomains.Domain c) :
 accepted c=test c := by
 unfold accepted
 rw [source c domain]
 cases test c <;> rfl

set_option pp.proofs false
#print source
#print axioms k
#print axioms source
#print axioms accepted_test
end NKL_ScanAtoms
end
