import NMS_ScanScalar
import NMS_RSLPoolCarriers
import NMS_RSLStepFacts
set_option autoImplicit false
noncomputable section
namespace NMS_RSLScan
open Aeneas Aeneas.Std AdapterRw
abbrev Candidate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
/-- The CLOSED scanner's one Box site follows the successful header/tag
checks. Allocation failure has no returned candidate or suffix events. -/
def raw {A : Type} (candidate : Candidate → A) (bytes : Slice U8) : RSL.RS (A × Nat) :=
 match AspisR1.NFY_JHf_Scan.source bytes with
 | .ok (.Ok scanned) =>
   RSL.RS.seq (RSL.RS.lift RSL.Spec.alloc)
    (RSL.RS.pure (candidate scanned.candidate_afterstate,scanned.proof_length.val))
 | .ok (.Err error) => RSL.RS.throw (NMS_RSLError.error error)
 | .fail _ => RSL.Spec.panic
 | .div => fun _ o => o = ⟨.diverge,[]⟩

theorem raw_extent {A : Type} (candidate : Candidate → A) (bytes : Slice U8)
 (env : RSL.Env) (scanned : A × Nat) (events : List RSL.Event)
 (run : raw candidate bytes env ⟨.ret (.ok scanned),events⟩) : scanned.2 = RSL.PROOF_BYTES := by
 unfold raw at run
 cases hs : AspisR1.NFY_JHf_Scan.source bytes with
 | ok reply =>
   cases reply with
   | Ok source =>
     simp only [hs] at run
     obtain ⟨_,_,_,_,last,_⟩ := NMS_RSLRefine.rsbind_return _ _ _ _ _ run
     have same := Except.ok.inj (RSL.Exit.ret.inj (congrArg RSL.Obs.exit last))
     have result := congrArg Prod.snd same
     exact result.trans (NMS_ScanScalar.proof_value bytes source hs)
   | Err error =>
     simp only [hs] at run
     have impossible := congrArg RSL.Obs.exit run
     cases impossible
 | fail error => simp only [hs] at run; cases run
 | div => simp only [hs] at run; cases run

def input (bytes : RSL.Bytes) (bounded : bytes.length ≤ Usize.max) : Slice U8 :=
 ⟨bytes.map NMS_RSLScalars.raw8,by simpa only [List.length_map] using bounded⟩

/-- Total byte-carrier extension; nonphysical lengths fail the scanner's
length gate, rather than being truncated into an unrelated usize buffer. -/
def scanner {A : Type} (candidate : Candidate → A) (bytes : RSL.Bytes) : RSL.RS (A × Nat) :=
 if bounded : bytes.length ≤ Usize.max then raw candidate (input bytes bounded)
 else RSL.RS.throw .invalidAccountData

theorem extent {A : Type} (candidate : Candidate → A) (bytes : RSL.Bytes)
 (env : RSL.Env) (scanned : A × Nat) (events : List RSL.Event)
 (run : scanner candidate bytes env ⟨.ret (.ok scanned),events⟩) : scanned.2 = RSL.PROOF_BYTES := by
 unfold scanner at run
 split at run
 · exact raw_extent candidate _ env scanned events run
 · have impossible := congrArg RSL.Obs.exit run
   cases impossible

#print axioms raw_extent
#print axioms extent
end NMS_RSLScan
