import R1Z.ProverRw21FrontOutput
import R1Z.ProverRw21QueryLengths
import R1Z.ProverRw21NodeLengths
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21ProofOutput
open ProverRw21ProtocolOutput ProverRw21FrontOutput
open ProverCommitPublish43 (Bytes)

def queryBytes (t : Transcript) : Bytes :=
  ((List.ofFn (fun i => query (t.openings i))).map ProverCommitPublish43.queryBytes).flatten

def beforeNodes (t : Transcript) : Bytes := front t ++ queryBytes t

def nodeResult (t : Transcript) : Except ProverCommitPublish43.Error Bytes :=
  ProverCommitPublish43.slots (ProverRw21ProtocolOutput.slots t) (beforeNodes t)

theorem before_nodes_length (t : Transcript) : (beforeNodes t).length=28359 := by
  unfold beforeNodes queryBytes
  rw [List.length_append,front_length,ProverRw21QueryLengths.all]

theorem successful_length (t : Transcript) (result : Bytes) (h : nodeResult t=.ok result) :
    result.length=57607 := by
  have hn := ProverRw21NodeLengths.slots_length t _ _ h
  rw [before_nodes_length] at hn
  exact hn

theorem reference_proof (t : Transcript) :
    ProverCommitFront46.referenceProof (fields t)
      (List.ofFn (fun i => query (t.openings i))) (ProverRw21ProtocolOutput.slots t) = nodeResult t := by
  unfold ProverCommitFront46.referenceProof ProverCommitPublish43.assemble
  rw [reference_front]
  simp only [Except.bind,ProverCommitPublish43.query_exact]
  change (if (beforeNodes t).length≠28359 then .error .parse else
    (nodeResult t).bind (fun out => if out.length≠57607 then .error .parse else .ok out))=nodeResult t
  rw [before_nodes_length]
  simp only [ne_eq,not_true_eq_false,if_false]
  cases hn : nodeResult t with
  | error e => rfl
  | ok result =>
    simp only [Except.bind]
    rw [successful_length t result hn]
    rfl

#print axioms queryBytes
#print axioms beforeNodes
#print axioms nodeResult
#print axioms before_nodes_length
#print axioms successful_length
#print axioms reference_proof
end R1Z.ProverRw21ProofOutput
