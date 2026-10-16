import RawBoundedTrace
import R1ProgramLabelRestriction
import AspisV8R19.OracleProgramOps

/-! The canonical trace projection is an exact inverse on protocol
programs whose reachable addresses are canonical. Arbitrary raw prover
queries remain outside this premise; it applies only to the legacy sampler
programs, whose canonical-label property is already proved. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawBoundedProgram

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem trace_append (L : Nat) {A : Type} (xs ys : List (Bytes × A)) :
    RawBoundedTrace.trace L (xs ++ ys) =
      RawBoundedTrace.trace L xs ++ RawBoundedTrace.trace L ys := by
  simp [RawBoundedTrace.trace, CanonicalRawTrace.trace,
    PartialAddressTrace.Embedding.project, PartialAddressTrace.Embedding.imageTrace,
    List.filterMap_append, List.map_append]

theorem trace_cons_canonical {L : Nat} {A : Type} (a : Addr L) (ha : CanonicalByteAddress.Canonical a)
    (v : A) (tr : List (Bytes × A)) :
    RawBoundedTrace.trace L ((a.toBytes,v)::tr) =
      (a,v)::RawBoundedTrace.trace L tr := by
  have hdec : (CanonicalRawTrace.embedding L).decode a.toBytes = some ⟨a,ha⟩ :=
    CanonicalRawTrace.decode_canonical L ⟨a,ha⟩
  unfold RawBoundedTrace.trace CanonicalRawTrace.trace
  rw [(CanonicalRawTrace.embedding L).project_cons_some _ _ _ ⟨a,ha⟩ hdec]
  rfl

theorem trace_map_canonical {L : Nat} {A : Type} (tr : List (Addr L × A))
    (hc : ∀ q ∈ tr, CanonicalByteAddress.Canonical q.1) :
    RawBoundedTrace.trace L (tr.map fun q => (q.1.toBytes,q.2)) = tr := by
  induction tr with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨a,v⟩ := q
      rw [List.map_cons, trace_cons_canonical a (hc (a,v) (List.mem_cons_self ..))]
      rw [ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))]

theorem labels_eval {I A O : Type} (C : I → Prop) (p : Program I A O)
    (h : ProgramLabelRestriction.AllLabels C p) (H : I → A) :
    ∀ q ∈ (eval H p).1, C q.1 := by
  induction p with
  | done o => simp [eval]
  | ask i next ih =>
      intro q hq
      simp only [eval, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h.1
      · exact ih (H i) (h.2 (H i)) q hq

theorem trace_eval_rename {L : Nat} {A O : Type} (p : Program (Addr L) A O)
    (hc : ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical p)
    (H : Bytes → A) :
    RawBoundedTrace.trace L (eval H (rename Addr.toBytes p)).1 =
      (eval (fun a => H a.toBytes) p).1 := by
  rw [eval_rename]
  change RawBoundedTrace.trace L
    ((eval (fun a => H a.toBytes) p).1.map fun q => (q.1.toBytes,q.2)) = _
  exact trace_map_canonical _ (labels_eval CanonicalByteAddress.Canonical p hc _)

/-- A deterministic trace-realizing program, used only inside an oracle-
fixed reuse proof. It is not a transformation of adversarial probability
laws and ignores all answers when choosing its supplied output. -/
def readTrace {I A O : Type} (tr : List (I × A)) (o : O) : Program I A O :=
  match tr with
  | [] => .done o
  | (i,_)::rest => .ask i (fun _ => readTrace rest o)

theorem eval_readTrace {I A O : Type} (H : I → A) (tr : List (I × A)) (o : O)
    (hc : ∀ q ∈ tr, q.2 = H q.1) : eval H (readTrace tr o) = (tr,o) := by
  induction tr with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨i,v⟩ := q
      have hv : v = H i := hc (i,v) (List.mem_cons_self ..)
      simp only [readTrace, eval, ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))]
      rw [hv]

#print axioms trace_append
#print axioms trace_map_canonical
#print axioms labels_eval
#print axioms trace_eval_rename
#print axioms eval_readTrace
end AspisR1.RawBoundedProgram
end
