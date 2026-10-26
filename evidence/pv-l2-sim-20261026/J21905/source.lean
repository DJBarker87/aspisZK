import R1Z.PV_L2_F3Recorded
import R1Z.PV_L2_F3SourceJoint

/-! The count law's source producer, with the failed read prefix retained.
Unlike Option.map, the outer pair does not discard observations on None.
This is an owned-source result, not native L1/ROM coupling evidence. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3FullSource
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.ProverCommitWordCarrier R1Z.ProverCommitSourceDecoder R1Z.ProverCommitOwnedDecoder
open R1Z.PV_L2_F3Recorded (Read)
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

def produce (hash : Hash) (domain : Slice U8) :
    Nat → Nat → State → Option (List (F × Nat)) × List Read
  | 0,_,_ => (some [],[])
  | _+1,0,_ => (none,[])
  | L+1,r+1,state =>
    let answer := prover_commit_reference.next hash domain state
    match answer with
    | .ok (word,after) =>
      if word &&& 2147483647#u32 < aspis_core.field.P then
        let rest := produce hash domain L 16 after
        (rest.1.map ((fieldValue (word &&& 2147483647#u32),17-(r+1))::·),
          ⟨state,answer⟩::rest.2)
      else
        let rest := produce hash domain (L+1) r after
        (rest.1,⟨state,answer⟩::rest.2)
    | _ => (none,[⟨state,answer⟩])
termination_by L r _ => 16*L+r

theorem erases (hash : Hash) (domain : Slice U8) (L r : Nat) (state : State) :
    (produce (K := K) hash domain L r state).1 =
      PV_L2_F3SourceCounts.source (K := K) hash domain L r state := by
  fun_induction produce (K := K) hash domain L r state <;>
    simp_all +zetaDelta [PV_L2_F3SourceCounts.source]

/-- Refill frames use the actual domain/seed/counter slices, in read order.
They include a failed hash call, rather than only successful decoded cells. -/
def requests (domain : Slice U8) (reads : List Read) : List (Slice (Slice U8)) :=
  reads.filterMap (PV_L2_F3Recorded.refill domain)

def sourceArrays (hash : Hash) (domain : Slice U8) (L : Nat) :=
  let result := produce (K := K) hash domain L 16 ProverCommitOwnedDecoder.initial
  (result.1.map (PV_L2_F3SourceArrays.splitList L),result.2)

theorem arrays_erases (hash : Hash) (domain : Slice U8) (L : Nat) :
    (sourceArrays (K := K) hash domain L).1 =
      PV_L2_F3SourceArrays.sourceArrays (K := K) hash domain L := by
  unfold sourceArrays PV_L2_F3SourceArrays.sourceArrays
  dsimp only
  rw [erases]

/-- Both caller prefixes survive if either source fails. The second caller
is reached only when the first succeeds, as in sourcePair. -/
def pair (input : ProverCommitSourceDecoder.Inputs) :
    Option ((((Fin L₁ → F) × (Fin L₂ → F))) × PV_L2_F3Tape.History) ×
      List Read × List Read :=
  let a := sourceArrays (K := K) (ProverCommitOwnedDecoder.blockHash input.1)
    AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN L₁
  match a.1 with
  | none => (none,a.2,[])
  | some av =>
    let b := sourceArrays (K := K) (ProverCommitOwnedDecoder.blockHash input.2)
      AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN L₂
    (b.1.map (fun bv => ((av.1,bv.1),(av.2,bv.2))),a.2,b.2)

theorem pair_erases (input : ProverCommitSourceDecoder.Inputs) :
    (pair (K := K) input).1 = PV_L2_F3SourceBudget.sourcePair (K := K) input := by
  unfold pair PV_L2_F3SourceBudget.sourcePair
  simp only [arrays_erases]
  cases a : PV_L2_F3SourceArrays.sourceArrays (K := K) (blockHash input.1)
    AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN L₁ with
  | none => rfl
  | some av =>
    cases b : PV_L2_F3SourceArrays.sourceArrays (K := K) (blockHash input.2)
      AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN L₂ <;> rfl

theorem observed_erases (input : ProverCommitSourceDecoder.Inputs) :
    (pair (K := K) input).1.map (PV_L2_F3Tape.outputEquiv (K := K)) =
      PV_L2_F3SourceJoint.sourceObserved (K := K) input := by
  rw [pair_erases]
  rfl

#print axioms erases
#print axioms arrays_erases
#print axioms pair_erases
#print axioms observed_erases
end R1Z.PV_L2_F3FullSource
