import Port11PROV_SourceCount
import Port9OR_P6Levels

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_Potential
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeNodeDomain MultiproofConeLevelIteration
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A feasible-code potential. Checked steps must return successfully; read
replies remain universal. Native hash failure is handled by count below. -/
def Funded {A : Type} (post : A → Nat) : Nat → Code A → Prop
  | n,.done a => post a ≤ n
  | n,.step r k => r ⦃ a => Funded post n (k a) ⦄
  | n,.read _ k => 0<n ∧ ∀ d, Funded post (n-1) (k d)

def credit (physical : Slice U8) (s : reference.Scratch) (i w : Usize) : Nat :=
  (physical.val.length-s.at.val)/32 + (s.n.val-i.val+w.val)-1

def rowPost (physical : Slice U8) : reference.Row → Nat
  | .Stop _ => 0
  | .Next s i w => credit physical s i w

def levelPost (physical : Slice U8) : reference.Level → Nat
  | .Stop _ => 0
  | .Done s => credit physical s 0#usize 0#usize

/-- Retains each physical read even if a later native hash fails/diverges. -/
theorem count {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (code : Code A) (post : A → Nat)
    (n : Nat) (funded : Funded post n code) :
    let out := eval H (Port9OR_Code.program D hash code)
    out.1.length + (match out.2 with | .ok a => post a | _ => 0) ≤ n := by
  induction code generalizing n with
  | done a => simpa only [Port9OR_Code.program,eval,List.length_nil,Nat.zero_add] using funded
  | step r k ih =>
    obtain ⟨a,ran,more⟩ := WP.spec_imp_exists funded
    simpa only [Port9OR_Code.program,ran,VTop_OracleCode.continueWith] using ih a n more
  | read parts k ih =>
    cases called : D.digest hash parts with
    | fail e => simpa only [Port9OR_Code.program,called,eval,List.length_nil,Nat.zero_add] using Nat.zero_le n
    | div => simpa only [Port9OR_Code.program,called,eval,List.length_nil,Nat.zero_add] using Nat.zero_le n
    | ok d =>
      have rest := ih (Port9OR_Reply.digest (H (AspisR1DigestLogCarrier.flatten parts))) (n-1)
        (funded.2 _)
      have positive := funded.1
      simp only [Port9OR_Code.program,called,eval,List.length_cons]
      omega

/-- The actual post-read checked writes preserve exact source cursors. -/
theorem finish_spec (physical : Slice U8) (s : reference.Scratch) (digest : Digest)
    (ni cursor : Usize) (index : U32) (w i : Usize)
    (domain : RowDomain physical s i w) (active : i.val<s.n.val) :
    MultiproofConePhysicalProgram.finish s digest ni cursor index w
      ⦃ out => match out with
        | .Stop _ => False
        | .Next next ni' nw => next.n=s.n ∧ next.«at»=cursor ∧ ni'=ni ∧ nw.val=w.val+1 ⦄ := by
  unfold MultiproofConePhysicalProgram.finish
  simp only [RowDomain] at domain
  step* <;> simp_all <;> scalar_tac

#print axioms count
#print axioms finish_spec
end AspisR1.Port12COUNT_Potential
end
