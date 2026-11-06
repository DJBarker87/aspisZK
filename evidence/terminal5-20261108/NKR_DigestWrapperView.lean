import NKR_DigestCuts
import NKR_ScheduleExt
/-! Reviewed native projection family from NKR_Digest_wrapper_window.rs.txt
SHA256 47486a32df5925a4bdab1e817fb0230e135b578344b66903fa603e1605048a67.
Assertions: `l.calls=1`, `l.seen=expected` at one arbitrary probe from all25
component kinds/coordinate families, and both returned cells equal reply.
The matched negative inverts exactly the selected payload assertion.
Native argument observations lift by ext below; no zero-input or output
assumption supplies the desired source result. P6/D188 option-A retained. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestWrapperView
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors)
open NJX_DigestCohort (D)
/-- One probe for every scalar or arbitrary raw-word coordinate checked by
NKR_Digest_wrapper_argument_window_cut; no field is omitted. -/
inductive Probe where
 | variant | pool (i : Fin 32) | domain (i : Fin 32)
 | anchor (i : Fin 8) | nullifier (i : Fin 8) | asset
 | recipientTag | recipient (i : Fin 8) | change (i : Fin 8)
 | amountTag | amount
 | sourcePool (i : Fin 32) | sourceDomain (i : Fin 32) | sequence | index
 | sourceRoot (i : Fin 8) | sourceFrontier (i : Fin 20) (j : Fin 8)
 | afterIndex | afterRoot (i : Fin 8) | afterFrontier (i : Fin 20) (j : Fin 8)
 | z (i : Fin 16) (j : Fin 4) | succ (i : Fin 16) (j : Fin 4) | xor12 (i : Fin 16) (j : Fin 4)
 | high (i : Fin 64) (j : Fin 4) | low (i : Fin 16) (j : Fin 4)

def words (q : NQ) : Fin 4 → U32 := ![q.c0.a,q.c0.b,q.c1.a,q.c1.b]
def variantCode : FIq_Native.pool_v1.pair_forest_semantic_terminal.CompiledVariant → Nat
 | .PrivateTransfer=>1 | .Withdrawal=>0
def tag {A : Type} (x : Option A) : Nat := if x.isSome then 1 else 0

def view (p : Public) (o : Openings) (s : Selectors) : Probe → Nat
 | .variant=>variantCode p.variant
 | .pool i=>(NJB_ArrayCarrier.cell p.pool i).val
 | .domain i=>(NJB_ArrayCarrier.cell p.deployment_domain i).val
 | .anchor i=>(NJB_ArrayCarrier.cell p.anchor i).val
 | .nullifier i=>(NJB_ArrayCarrier.cell p.nullifier i).val
 | .asset=>p.asset_id.val
 | .recipientTag=>tag p.recipient
 | .recipient i=>(p.recipient.map (fun d=>(NJB_ArrayCarrier.cell d i).val)).getD 0
 | .change i=>(NJB_ArrayCarrier.cell p.change i).val
 | .amountTag=>tag p.withdrawal_amount
 | .amount=>(p.withdrawal_amount.map UScalar.val).getD 0
 | .sourcePool i=>(NJB_ArrayCarrier.cell p.transition.live_snapshot.pool i).val
 | .sourceDomain i=>(NJB_ArrayCarrier.cell p.transition.live_snapshot.deployment_domain i).val
 | .sequence=>p.transition.live_snapshot.sequence.val
 | .index=>p.transition.live_snapshot.next_pair_index.val
 | .sourceRoot i=>(NJB_ArrayCarrier.cell p.transition.live_snapshot.current_root i).val
 | .sourceFrontier i j=>(NJB_ArrayCarrier.cell (NJB_ArrayCarrier.cell p.transition.live_snapshot.frontier i) j).val
 | .afterIndex=>p.transition.candidate_afterstate.next_pair_index.val
 | .afterRoot i=>(NJB_ArrayCarrier.cell p.transition.candidate_afterstate.next_root i).val
 | .afterFrontier i j=>(NJB_ArrayCarrier.cell (NJB_ArrayCarrier.cell p.transition.candidate_afterstate.next_frontier i) j).val
 | .z i j=>(words (NJB_ArrayCarrier.cell o.z i) j).val
 | .succ i j=>(words (NJB_ArrayCarrier.cell o.succ_z i) j).val
 | .xor12 i j=>(words (NJB_ArrayCarrier.cell o.xor12_z i) j).val
 | .high i j=>(words (NJB_ArrayCarrier.cell s.high i) j).val
 | .low i j=>(words (NJB_ArrayCarrier.cell s.low i) j).val

theorem qm (a b : NQ) (h : ∀ j,(words a j).val=(words b j).val) : a=b := by
 have h0 : a.c0.a=b.c0.a := UScalar.eq_of_val_eq (h 0)
 have h1 : a.c0.b=b.c0.b := UScalar.eq_of_val_eq (h 1)
 have h2 : a.c1.a=b.c1.a := UScalar.eq_of_val_eq (h 2)
 have h3 : a.c1.b=b.c1.b := UScalar.eq_of_val_eq (h 3)
 rcases a with ⟨⟨a0,a1⟩,⟨a2,a3⟩⟩
 rcases b with ⟨⟨b0,b1⟩,⟨b2,b3⟩⟩
 cases h0;cases h1;cases h2;cases h3
 rfl

theorem byteArray {n : Usize} (a b : Array U8 n)
 (h : ∀ i,(NJB_ArrayCarrier.cell a i).val=(NJB_ArrayCarrier.cell b i).val) : a=b :=
 NKR_ScheduleExt.array a b (fun i=>UScalar.eq_of_val_eq (h i))
theorem wordArray {n : Usize} (a b : Array U32 n)
 (h : ∀ i,(NJB_ArrayCarrier.cell a i).val=(NJB_ArrayCarrier.cell b i).val) : a=b :=
 NKR_ScheduleExt.array a b (fun i=>UScalar.eq_of_val_eq (h i))
theorem qmArray {n : Usize} (a b : Array NQ n)
 (h : ∀ i j,(words (NJB_ArrayCarrier.cell a i) j).val=(words (NJB_ArrayCarrier.cell b i) j).val) : a=b :=
 NKR_ScheduleExt.array a b (fun i=>qm _ _ (h i))

theorem optionWord (a b : Option U32) (ht : tag a=tag b)
 (hv : (a.map UScalar.val).getD 0=(b.map UScalar.val).getD 0) : a=b := by
 cases a with
 | none=>cases b with
   | none=>rfl
   | some b=>simp [tag] at ht
 | some a=>cases b with
   | none=>simp [tag] at ht
   | some b=>exact congrArg some (UScalar.eq_of_val_eq hv)

theorem optionDigest (a b : Option D) (ht : tag a=tag b)
 (hv : ∀ i,(a.map (fun d=>(NJB_ArrayCarrier.cell d i).val)).getD 0=(b.map (fun d=>(NJB_ArrayCarrier.cell d i).val)).getD 0) : a=b := by
 cases a with
 | none=>cases b with
   | none=>rfl
   | some b=>simp [tag] at ht
 | some a=>cases b with
   | none=>simp [tag] at ht
   | some b=>exact congrArg some (wordArray a b hv)

theorem variant (a b : FIq_Native.pool_v1.pair_forest_semantic_terminal.CompiledVariant)
 (h : variantCode a=variantCode b) : a=b := by
 cases a <;> cases b <;> simp_all [variantCode]

theorem openings (a b : Openings) (hz : a.z=b.z) (hs : a.succ_z=b.succ_z) (hx : a.xor12_z=b.xor12_z) : a=b := by
 cases a;cases b;simp_all

theorem selectors (a b : Selectors) (hh : a.high=b.high) (hl : a.low=b.low) : a=b := by
 cases a;cases b;simp_all

/-- Exact full-carrier extensionality from the one-probe native argument
family. No canonicality, zero representative, output or pointer hypothesis. -/
theorem ext (p p' : Public) (o o' : Openings) (s s' : Selectors)
 (h : ∀ probe,view p o s probe=view p' o' s' probe) : p=p' ∧ o=o' ∧ s=s' := by
 have srcPool:=byteArray p.transition.live_snapshot.pool p'.transition.live_snapshot.pool (fun i=>h (.sourcePool i))
 have srcDomain:=byteArray p.transition.live_snapshot.deployment_domain p'.transition.live_snapshot.deployment_domain (fun i=>h (.sourceDomain i))
 have srcRoot:=wordArray p.transition.live_snapshot.current_root p'.transition.live_snapshot.current_root (fun i=>h (.sourceRoot i))
 have srcFrontier:=NKR_ScheduleExt.array p.transition.live_snapshot.frontier p'.transition.live_snapshot.frontier
  (fun i=>wordArray (NJB_ArrayCarrier.cell p.transition.live_snapshot.frontier i) (NJB_ArrayCarrier.cell p'.transition.live_snapshot.frontier i) (fun j=>h (.sourceFrontier i j)))
 have source:=NKR_ScheduleExt.snapshot p.transition.live_snapshot p'.transition.live_snapshot srcPool srcDomain
  (UScalar.eq_of_val_eq (h .sequence)) (UScalar.eq_of_val_eq (h .index)) srcRoot srcFrontier
 have afterRoot:=wordArray p.transition.candidate_afterstate.next_root p'.transition.candidate_afterstate.next_root (fun i=>h (.afterRoot i))
 have afterFrontier:=NKR_ScheduleExt.array p.transition.candidate_afterstate.next_frontier p'.transition.candidate_afterstate.next_frontier
  (fun i=>wordArray (NJB_ArrayCarrier.cell p.transition.candidate_afterstate.next_frontier i) (NJB_ArrayCarrier.cell p'.transition.candidate_afterstate.next_frontier i) (fun j=>h (.afterFrontier i j)))
 have after:=NKR_ScheduleExt.afterstate p.transition.candidate_afterstate p'.transition.candidate_afterstate (UScalar.eq_of_val_eq (h .afterIndex)) afterRoot afterFrontier
 have pub:=NKR_ScheduleExt.semanticPublic p p' (variant p.variant p'.variant (h .variant))
  (byteArray p.pool p'.pool (fun i=>h (.pool i))) (byteArray p.deployment_domain p'.deployment_domain (fun i=>h (.domain i)))
  (wordArray p.anchor p'.anchor (fun i=>h (.anchor i))) (wordArray p.nullifier p'.nullifier (fun i=>h (.nullifier i)))
  (UScalar.eq_of_val_eq (h .asset)) (optionDigest p.recipient p'.recipient (h .recipientTag) (fun i=>h (.recipient i)))
  (wordArray p.change p'.change (fun i=>h (.change i))) (optionWord p.withdrawal_amount p'.withdrawal_amount (h .amountTag) (h .amount))
  (NKR_ScheduleExt.transition p.transition p'.transition source after)
 exact ⟨pub,openings o o' (qmArray o.z o'.z (fun i j=>h (.z i j)))
  (qmArray o.succ_z o'.succ_z (fun i j=>h (.succ i j))) (qmArray o.xor12_z o'.xor12_z (fun i j=>h (.xor12 i j))),
  selectors s s' (qmArray s.high s'.high (fun i j=>h (.high i j))) (qmArray s.low s'.low (fun i j=>h (.low i j)))⟩

/-- The same precise raw-coordinate extension discharges the split middle
append-window's full frontier/opened/high argument carrier. Native inputs
are already fully arbitrary; this is not representative generalization. -/
theorem appendArguments (f f' : NJX_AppendDomains.Frontier) (o o' : NJX_DigestCohort.O)
 (s s' : NJX_AppendDomains.High)
 (hf : ∀ i j,(NJB_ArrayCarrier.cell (NJB_ArrayCarrier.cell f i) j).val=
  (NJB_ArrayCarrier.cell (NJB_ArrayCarrier.cell f' i) j).val)
 (ho : ∀ i j,(words (NJB_ArrayCarrier.cell o i) j).val=(words (NJB_ArrayCarrier.cell o' i) j).val)
 (hs : ∀ i j,(words (NJB_ArrayCarrier.cell s i) j).val=(words (NJB_ArrayCarrier.cell s' i) j).val) :
 f=f' ∧ o=o' ∧ s=s' :=
 ⟨NKR_ScheduleExt.array f f' (fun i=>wordArray _ _ (hf i)),qmArray o o' ho,qmArray s s' hs⟩

/-- Every middle segment's asserted group/lane/raw-limb post covers the
complete arbitrary3x2state, including the framed groups. -/
theorem post (a b : NKR_DigestCuts.Sums)
 (h : ∀ g j k,(words (a g j) k).val=(words (b g j) k).val) : a=b := by
 funext g j
 exact qm _ _ (h g j)
#print axioms appendArguments
#print axioms post

/-- Primitive transcription of the NEW actual-wrapper projected native
window: one call, one universally selected component, and both return cells.
Full record equality is a theorem below, not an extra primitive assertion. -/
def NativeCut (p : Public) (o : Openings) (s : Selectors) (seenP : Public) (seenO : Openings)
 (seenS : Selectors) (reply out : NKR_DigestChildren.Pair) (calls : Nat) : Prop :=
 calls=1 ∧ (∀ probe,view seenP seenO seenS probe=view p o s probe) ∧ out=reply

theorem native_cut (p : Public) (o : Openings) (s : Selectors) (reply : NKR_DigestChildren.Pair) :
 NativeCut p o s p o s reply reply 1 := ⟨rfl,fun _=>rfl,rfl⟩
#print axioms native_cut

/-- Strong WrapperCut follows from exactly the selected payload assertions
and both returned cells. This is a support composition, not a root premise. -/
theorem wrapper_cut (p seenP : Public) (o seenO : Openings) (s seenS : Selectors)
 (reply out : NKR_DigestChildren.Pair) (calls : Nat) (hc : calls=1)
 (h : ∀ probe,view seenP seenO seenS probe=view p o s probe) (hr : out=reply) :
 NKR_DigestCuts.WrapperCut p o s seenP seenO seenS reply out calls := by
 obtain ⟨hp,ho,hs⟩ := ext seenP p seenO o seenS s h
 exact ⟨hc,hp,ho,hs,hr⟩
/-- Derived full wrapper summary from precisely the NEW native probe
family; no whole-record assertion or retired K022 credit is used. -/
theorem native_summary (p seenP : Public) (o seenO : Openings) (s seenS : Selectors)
 (reply out : NKR_DigestChildren.Pair) (calls : Nat)
 (h : NativeCut p o s seenP seenO seenS reply out calls) :
 NKR_DigestCuts.WrapperCut p o s seenP seenO seenS reply out calls :=
 wrapper_cut p seenP o seenO s seenS reply out calls h.1 h.2.1 h.2.2
#print axioms native_summary

#print axioms qm
#print axioms byteArray
#print axioms wordArray
#print axioms qmArray
#print axioms optionWord
#print axioms optionDigest
#print axioms variant
#print axioms openings
#print axioms selectors
#print axioms ext
#print axioms wrapper_cut
end AspisR1.NKR_DigestWrapperView
end
