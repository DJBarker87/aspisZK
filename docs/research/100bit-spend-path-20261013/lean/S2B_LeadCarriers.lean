import RawDigestLogCarrier
import AspisV8R19.SqueezeOracleBridge
import CheckpointBytes5Effect

/-! Package-independent carriers, as required by RawDigestLogCarrier's existing
extraction-collision boundary. These implications consume one execution index;
they do not construct a native execution certificate or reify verifierOps. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2B_LeadCarriers
open AspisV8R19.DuplexFrames AspisR1DigestLogCarrier
open CheckpointBytes5Effect

def bytesOf (xs : List U8) : Bytes := xs.map decodeByte
def observe (log : Log) : List (Bytes × AspisR1DigestLogCarrier.State) :=
  log.map (fun call => (flatten call.1,decodeState call.2))

/-- The supplied source-range conclusions transport to the common carrier.
bytesOf is definitionally the lead's MultiproofConeCanonical.bytesOf. -/
theorem proof_bytes {Execution : Type} (E : Execution)
    (selected : Execution → Slice U8) (original : alloc.vec.Vec U8)
    (shape : (selected E).val = (original.val.drop 688).take 57607)
    (width : (selected E).val.length = 57607)
    (split : original.val = original.val.take 688 ++ (selected E).val) :
    bytesOf (selected E).val = ((bytesOf original.val).drop 688).take 57607 ∧
    (bytesOf (selected E).val).length = 57607 ∧
    bytesOf original.val = (bytesOf original.val).take 688 ++ bytesOf (selected E).val := by
  refine ⟨?_,?_,?_⟩
  · rw [shape]
    simp only [bytesOf,List.map_take,List.map_drop]
  · simpa only [bytesOf,List.length_map] using width
  · have mapped := congrArg bytesOf split
    simpa only [bytesOf,List.map_append,List.map_take] using mapped

/-- The success-conditioned predicate is definitionally the checkpoint cone's
Oracle after substituting its digest field; no decoder package import is needed.
The total physical/raw-oracle law remains a premise. -/
theorem digest_children {Execution : Type} (E : Execution)
    (hashv : Execution → Parts → Result Digest) (H : Bytes → AspisR1DigestLogCarrier.State)
    (law : ∀ parts, hashv E parts = ok
      (AspisV8R19.SqueezeOracleBridge.encodeState (H (flatten parts)))) :
    ∀ parts digest, hashv E parts = ok digest → decodeState digest = H (flatten parts) := by
  intro parts digest success
  have same := Result.ok.inj ((law parts).symm.trans success)
  subst digest
  change AspisV8R19.SqueezeOracleBridge.decodeState
    (AspisV8R19.SqueezeOracleBridge.encodeState (H (flatten parts))) = _
  exact AspisV8R19.SqueezeOracleBridge.state_roundtrip _

/-- Every successful stateful child, including an inner verifier Err, preserves
consistency of the actual ordered log. This is derived from the reified run,
not from a freely supplied list of successful digest observations. Native child
reification and per-call backend interpretation remain separate obligations. -/
theorem ordered_calls {Execution A Hash : Type} (E : Execution)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → AspisR1DigestLogCarrier.State)
    (child : Execution → Code A) (before after : Log) (value : A)
    (oracle : ∀ parts digest, D.digest hash parts = ok digest →
      decodeState digest = H (flatten parts))
    (initial : Consistent H (observe before))
    (returned : run D hash (child E) before = ok (value,after)) :
    Consistent H (observe after) := by
  generalize child E = code at returned
  induction code generalizing before after with
  | done a =>
    have same := Result.ok.inj returned
    have logs := congrArg Prod.snd same
    change before = after at logs
    rw [←logs]
    exact initial
  | step r next ih =>
    cases r with
    | fail e => cases returned
    | div => cases returned
    | ok a => exact ih a before after initial returned
  | read parts next ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [run,call,bind_tc_fail] at returned; cases returned
    | div => simp only [run,call,bind_tc_div] at returned; cases returned
    | ok digest =>
      simp only [run,call,bind_tc_ok] at returned
      have singleton : Consistent H [(flatten parts,decodeState digest)] := by
        intro q hq
        have same := List.mem_singleton.mp hq
        subst q
        exact oracle parts digest call
      have extended : Consistent H (observe (before ++ [(parts,digest)])) := by
        change Consistent H ((before ++ [(parts,digest)]).map _)
        rw [List.map_append]
        exact append_consistent H _ _ initial singleton
      exact ih digest _ _ extended returned

#print axioms proof_bytes
#print axioms digest_children
#print axioms ordered_calls
end AspisR1.S2B_LeadCarriers
