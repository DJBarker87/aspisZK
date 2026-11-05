import Lean
import NFY_Part059
import NFY_Part058
import NFY_Part052

-- BEGIN copied NFD_RequestField03: evidence/slice-s-compose10-20261104/NFD_RequestField03.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField03
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => 1
 | .Withdrawal p => 2
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨3,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField03
-- END copied NFD_RequestField03
-- BEGIN copied NFD_RequestField04: evidence/slice-s-compose10-20261104/NFD_RequestField04.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField04
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => (get p.pool j).val
 | .Withdrawal p => (get p.pool j).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨4,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField04
-- END copied NFD_RequestField04
-- BEGIN copied NFD_RequestField05: evidence/slice-s-compose10-20261104/NFD_RequestField05.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField05
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => (get p.deployment_domain j).val
 | .Withdrawal p => (get p.deployment_domain j).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨5,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField05
-- END copied NFD_RequestField05
-- BEGIN copied NFD_RequestField06: evidence/slice-s-compose10-20261104/NFD_RequestField06.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField06
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => p.anchor_sequence.val
 | .Withdrawal p => p.anchor_sequence.val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨6,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField06
-- END copied NFD_RequestField06
-- BEGIN copied NFD_RequestField07: evidence/slice-s-compose10-20261104/NFD_RequestField07.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField07
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => (get p.anchor_root i).val
 | .Withdrawal p => (get p.anchor_root i).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨7,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField07
-- END copied NFD_RequestField07
-- BEGIN copied NFD_RequestField08: evidence/slice-s-compose10-20261104/NFD_RequestField08.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField08
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => (get p.nullifier i).val
 | .Withdrawal p => (get p.nullifier i).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨8,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField08
-- END copied NFD_RequestField08
-- BEGIN copied NFD_RequestField09: evidence/slice-s-compose10-20261104/NFD_RequestField09.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField09
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => p.asset_id.val
 | .Withdrawal p => p.asset_id.val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨9,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField09
-- END copied NFD_RequestField09
-- BEGIN copied NFD_RequestField10: evidence/slice-s-compose10-20261104/NFD_RequestField10.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField10
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => (get p.change_commitment i).val
 | .Withdrawal p => (get p.change_commitment i).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨10,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField10
-- END copied NFD_RequestField10
-- BEGIN copied NFD_RequestField11: evidence/slice-s-compose10-20261104/NFD_RequestField11.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField11
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => (get p.recipient_commitment i).val
 | .Withdrawal p => 0
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨11,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField11
-- END copied NFD_RequestField11
-- BEGIN copied NFD_RequestField12: evidence/slice-s-compose10-20261104/NFD_RequestField12.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField12
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => 0
 | .Withdrawal p => p.amount.val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨12,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField12
-- END copied NFD_RequestField12
-- BEGIN copied NFD_RequestField13: evidence/slice-s-compose10-20261104/NFD_RequestField13.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField13
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 match s.«public» with
 | .PrivateTransfer p => 0
 | .Withdrawal p => (get p.destination_token_account j).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨13,by decide⟩ i j=expected s i j := by
  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl

#print axioms alignment
end NFY_NFD_RequestField13
-- END copied NFD_RequestField13
-- BEGIN copied NEU_EqualityLoop: evidence/slice-s-compose7-20261103/NEU_EqualityLoop.lean
set_option autoImplicit false
namespace NFY_NEU_EqualityLoop
open Aeneas Aeneas.Std

def equalBytes (left right : List U8) : Bool :=
  match left,right with
  | [],[] => true
  | a::left,b::right => decide (a=b) && equalBytes left right
  | _,_ => false

/-- Symbolic induction; no concrete688-byte recurrence is normalized. -/
theorem prefix_exact (left right : List U8) : equalBytes left right=true ↔ left=right := by
  induction left generalizing right with
  | nil => cases right <;> simp [equalBytes]
  | cons a left ih => cases right <;> simp [equalBytes,ih]

/-- Arbitrary prestate accumulator is retained by one equality window. -/
theorem step_invariant (a b : U8) (same : Bool) :
    (same && decide (a=b))=true ↔ same=true ∧ a=b := by simp

theorem prefix_frame {State : Type} (left right : List U8) (state : State) :
    (equalBytes left right,state,([] : List Unit)) =
    (decide (left=right),state,[]) := by
  have eqv := prefix_exact left right
  have same : equalBytes left right=decide (left=right) := by
    cases h : equalBytes left right <;> simp_all
  rw [same]

#print axioms prefix_exact
#print axioms step_invariant
#print axioms prefix_frame
end NFY_NEU_EqualityLoop
-- END copied NEU_EqualityLoop
-- BEGIN copied NFD_ScanConditional: evidence/slice-s-compose10-20261104/NFD_ScanConditional.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_ScanConditional
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal
/-- OPEN native/compiler/library obligation: the reached 688-byte comparison
must agree with bytewise equality on the SAME two live buffers. -/
def NativeEqualityAssociation (equality : List U8 → List U8 → Bool) : Prop :=
  ∀ left right, equality left right = decide (left=right)

def run (equality : List U8 → List U8 → Bool) (bytes : Slice U8) : Result (core.result.Result
    AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError) := do
  let expected ← lift (Usize.checked_add 688#usize 57607#usize)
  match expected with
  | none=>ok (.Err .InvalidAccountData)
  | some size=>
    if Slice.len bytes != size then ok (.Err .InvalidAccountData) else do
      let header ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start:=0#usize,«end»:=688#usize}
      let decoded ← decode_pool_v1_pair_verified_afterstate_v1 header
      match decoded with
      | .Err _=>ok (.Err .InvalidAccountData)
      | .Ok candidate=>
        let encoded ← encode_pool_v1_pair_verified_afterstate_v1 candidate
        match encoded with
        | .Err _=>ok (.Err .InvalidAccountData)
        | .Ok encoded=>
          if equality encoded.val header.val = false then ok (.Err .InvalidAccountData) else do
            let tag ← Slice.index_usize bytes 696#usize
            if tag != 2#u8 then ok (.Err .InvalidAccountData) else
              ok (.Ok ⟨AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 candidate,57607#usize⟩)

/-- Conditional root MODEL theorem. The named equality bridge is explicitly
retained, so this is not a CLOSED native root certificate. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State)
    (equality : List U8 → List U8 → Bool)
    (nativeEqualityBridge : NativeEqualityAssociation equality) :
    (run equality bytes,state,([] : List Unit)) =
    (AspisR1.NFY_JHf_Scan.source bytes,state,[]) := by
  unfold NativeEqualityAssociation at nativeEqualityBridge
  unfold run AspisR1.NFY_JHf_Scan.source
  simp only [nativeEqualityBridge,decide_eq_false_iff_not,bne_iff_ne]
  rfl

#print axioms result_state_effects
#print axioms NFY_NEU_EqualityLoop.prefix_exact
#print axioms NFY_NEU_EqualityLoop.step_invariant
end NFY_NFD_ScanConditional
-- END copied NFD_ScanConditional
-- BEGIN copied NFH_ComparisonBoundary: evidence/slice-s-compose11-20261104/NFH_ComparisonBoundary.lean
set_option autoImplicit false
namespace NFY_NFH_ComparisonBoundary
open Aeneas Aeneas.Std

/-- Proposed, NOT adopted: only the zero/nonzero observation is needed.
No lexicographic sign or magnitude claim is required by the scanner. -/
def ZeroLaw (left right : List U8) (reply : Int) : Prop :=
  reply = 0 ↔ left = right

/-- Sufficiency reuses the existing symbolic byte-loop proof. The runtime
law remains a named hypothesis; this is SUPPORT, not native closure. -/
theorem reply_eq_loop (left right : List U8) (reply : Int)
    (runtimeZeroLaw : ZeroLaw left right reply) :
    decide (reply = 0) = NFY_NEU_EqualityLoop.equalBytes left right := by
  have loop := NFY_NEU_EqualityLoop.prefix_frame left right ()
  have exactLoop : NFY_NEU_EqualityLoop.equalBytes left right = decide (left = right) :=
    congrArg Prod.fst loop
  rw [exactLoop]
  by_cases h : reply = 0 <;> simp_all [ZeroLaw]

/-- Necessity prevents passing an unconstrained syscall reply as a proof of
native equality. The same two list values occur on both sides. -/
theorem zeroLaw_necessary (left right : List U8) (reply : Int)
    (association : decide (reply = 0) = NFY_NEU_EqualityLoop.equalBytes left right) :
    ZeroLaw left right reply := by
  unfold ZeroLaw
  have loop := NFY_NEU_EqualityLoop.prefix_exact left right
  rw [← association] at loop
  simpa only [decide_eq_true_eq] using loop

/-- Even equal688-byte buffers do not constrain an opaque integer reply.
No concrete recurrence or large numeral is evaluated. -/
theorem opaque_reply_insufficient (left : List U8) :
    ∃ reply : Int, ¬ ZeroLaw left left reply := by
  exact ⟨1, by simp [ZeroLaw]⟩

#print axioms reply_eq_loop
#print axioms zeroLaw_necessary
#print axioms opaque_reply_insufficient
end NFY_NFH_ComparisonBoundary
-- END copied NFH_ComparisonBoundary
-- BEGIN copied NFH_ComparisonDomain: evidence/slice-s-compose11-20261104/NFH_ComparisonDomain.lean
set_option autoImplicit false
namespace NFY_NFH_ComparisonDomain
open Aeneas Aeneas.Std
open NFY_NFH_ComparisonBoundary

/-- Only the reached688-byte domain is proposed for runtime certification. -/
def At688Law (reply : List U8 → List U8 → Int) : Prop :=
  ∀ left right, left.length = 688 → right.length = 688 →
    ZeroLaw left right (reply left right)

/-- Mathematical completion outside the native call domain. It has no native
credit: the caller must separately establish both actual buffer lengths. -/
def complete688 (reply : List U8 → List U8 → Int) (left right : List U8) : Bool :=
  if left.length = 688 ∧ right.length = 688 then decide (reply left right = 0)
  else NFY_NEU_EqualityLoop.equalBytes left right

theorem complete688_on_domain (reply : List U8 → List U8 → Int)
    (left right : List U8) (leftSize : left.length = 688)
    (rightSize : right.length = 688) :
    complete688 reply left right = decide (reply left right = 0) := by
  simp only [complete688,leftSize,rightSize,and_self,if_true]

/-- Conditional interface conversion, not discharge of At688Law and not a
scanner theorem. No runtime fact about other lengths is assumed. -/
theorem complete688_association (reply : List U8 → List U8 → Int)
    (runtime688Law : At688Law reply) :
    NFY_NFD_ScanConditional.NativeEqualityAssociation (complete688 reply) := by
  intro left right
  have loop : NFY_NEU_EqualityLoop.equalBytes left right = decide (left = right) :=
    congrArg Prod.fst (NFY_NEU_EqualityLoop.prefix_frame left right ())
  unfold complete688
  split
  next sizes =>
    rw [reply_eq_loop left right (reply left right)
      (runtime688Law left right sizes.1 sizes.2)]
    exact loop
  next => exact loop

#print axioms complete688_on_domain
#print axioms complete688_association
end NFY_NFH_ComparisonDomain
-- END copied NFH_ComparisonDomain
-- BEGIN copied NFJ_Comparison: evidence/slice-s-compose12-20261104/NFJ_Comparison.lean
set_option autoImplicit false
namespace NFY_NFJ_Comparison
open Aeneas Aeneas.Std

/-- RuntimeMemcmp (ac), ADDED trust, pending owner confirmation.
Only the zero law for the SAME two retained 688-byte ranges is consumed here.
Normal return, result-slot identity and the observable frame are the separate
native forwarding certificate and the explicitly named runtime row. -/
abbrev RuntimeMemcmp := NFY_NFH_ComparisonDomain.At688Law

def header (bytes : List U8) : List U8 := bytes.take 688

theorem header_length (bytes : List U8) (acceptedLength : bytes.length = 58295) :
    (header bytes).length = 688 := by
  simp only [header,List.length_take,acceptedLength]
  rfl

theorem same_buffer_lengths (bytes : List U8) (acceptedLength : bytes.length = 58295)
    (encoded : Array U8 688#usize) :
    encoded.val.length = 688 ∧ (header bytes).length = 688 :=
  ⟨encoded.property,header_length bytes acceptedLength⟩

/-- This applies the 688-only law AFTER establishing both SAME buffer lengths;
it never asserts a runtime law for another length. -/
theorem nativeEqualityBridge (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : RuntimeMemcmp reply) (bytes : List U8)
    (acceptedLength : bytes.length = 58295) (encoded : Array U8 688#usize) :
    decide (reply encoded.val (header bytes) = 0) =
      NFY_NFH_ComparisonDomain.complete688 reply encoded.val (header bytes) := by
  exact (NFY_NFH_ComparisonDomain.complete688_on_domain reply encoded.val (header bytes)
    (same_buffer_lengths bytes acceptedLength encoded).1
    (same_buffer_lengths bytes acceptedLength encoded).2).symm

/-- Equal and unequal branches use exactly the slot's zero observation. -/
theorem slot_zero_iff (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : RuntimeMemcmp reply) (bytes : List U8)
    (acceptedLength : bytes.length = 58295) (encoded : Array U8 688#usize) :
    reply encoded.val (header bytes) = 0 ↔ encoded.val = header bytes := by
  exact runtimeMemcmp encoded.val (header bytes) encoded.property
    (header_length bytes acceptedLength)

/-- The mathematical completion supplies the old universal MODEL interface;
only nativeEqualityBridge above licenses native use on the reached domain. -/
theorem completion (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : RuntimeMemcmp reply) :
    NFY_NFD_ScanConditional.NativeEqualityAssociation
      (NFY_NFH_ComparisonDomain.complete688 reply) :=
  NFY_NFH_ComparisonDomain.complete688_association reply runtimeMemcmp

#print axioms header_length
#print axioms same_buffer_lengths
#print axioms nativeEqualityBridge
#print axioms slot_zero_iff
#print axioms completion
end NFY_NFJ_Comparison
-- END copied NFJ_Comparison
-- BEGIN copied NFJ_Scanner: evidence/slice-s-compose12-20261104/NFJ_Scanner.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFJ_Scanner
open Aeneas Aeneas.Std Result

/-- Mathematical execution model; completion is used only off the native
688-byte call domain. RuntimeMemcmp(ac) is explicitly retained as ADDED trust. -/
def run (reply : List U8 → List U8 → Int) (bytes : Slice U8) :=
  NFY_NFD_ScanConditional.run (NFY_NFH_ComparisonDomain.complete688 reply) bytes

/-- Scanner root MODEL theorem. Native forwarding and CLOSED callee packets
supply the separate ruling-(y) hybrid source link. No inner callee bridge,
PacketDomain or PhysicalInterpretation hypothesis is introduced here. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State)
    (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : NFY_NFJ_Comparison.RuntimeMemcmp reply) :
    (run reply bytes,state,([] : List Unit)) =
    (AspisR1.NFY_JHf_Scan.source bytes,state,[]) :=
  NFY_NFD_ScanConditional.result_state_effects bytes state _
    (NFY_NFJ_Comparison.completion reply runtimeMemcmp)

/-- The successful encode carrier, including arbitrary error replies before
it is reached, has exactly the native fixed-array width. -/
theorem encode_domain (encoded : Array U8 688#usize) :
    encoded.to_slice.val.length = 688 := encoded.property

/-- Same reached decode range: no independent bytes or success witness. -/
theorem decode_domain (bytes : List U8) (length : bytes.length = 58295) :
    (NFY_NFJ_Comparison.header bytes).length = 688 :=
  NFY_NFJ_Comparison.header_length bytes length

/-- The only tag call is S2; the adopted source continuation tests byte696
against2. The native callsite uses the CLOSED Variant::tag packet. -/
theorem tag_domain (tag : U8) :
    (tag != 2#u8) = false ↔ tag = 2#u8 := by
  simp

#print axioms result_state_effects
#print axioms encode_domain
#print axioms decode_domain
#print axioms tag_domain
end NFY_NFJ_Scanner
-- END copied NFJ_Scanner

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
