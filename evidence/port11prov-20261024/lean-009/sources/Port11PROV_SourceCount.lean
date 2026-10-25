import Port9OR_Budget
import Port9OR_P6Rows
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_SourceCount
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port9OR_Budget

theorem mono {A : Type} (code : Code A) (n m : Nat)
    (h : n≤m) (boundedN : bounded n code) : bounded m code := by
  induction code generalizing n m with
  | done a => trivial
  | step r c ih => exact fun b => ih b n m h (boundedN b)
  | read parts c ih =>
    refine ⟨by have := boundedN.1; omega,?_⟩
    intro b
    exact ih b (n-1) (m-1) (by omega) (boundedN.2 b)

/-- Structural composition used below on the concrete emitted physical code. -/
theorem bind_bound {A B : Type} (p : Code A) (k : A → Code B) (n m : Nat)
    (hp : bounded n p) (hk : ∀ a, bounded m (k a)) : bounded (n+m) (p >>= k) := by
  induction p generalizing n with
  | done a => exact mono (k a) m (n+m) (by omega) (hk a)
  | step r c ih => exact fun b => ih b n (hp b)
  | read parts c ih =>
    change 0<n+m ∧ ∀ b, bounded (n+m-1) (CheckpointBytes5Effect.bind (c b) k)
    constructor
    · have := hp.1; omega
    · intro b
      have eq : n+m-1=(n-1)+m := by have := hp.1; omega
      rw [eq]
      exact ih b (n-1) (hp.2 b)

/-- Hash-before-write includes a hash whose post-hash mutation later fails. -/
theorem parent_bound (s : reference.Scratch) (left right : Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) :
    bounded 1 (Port9OR_P6Node.parent s left right ni cursor index w) := by
  simp only [Port9OR_P6Node.parent,bounded,liftResult]
  exact ⟨by decide,fun _ _ => trivial⟩

/-- Every supplied/occupied sibling branch, including short buffer rejection. -/
theorem node_bound (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    bounded 1 (Port9OR_P6Node.node s physical i w) := by
  unfold Port9OR_P6Node.node
  repeat' first
  | (solve | apply parent_bound)
  | (solve | trivial)
  | (fail_if_no_progress simp only [bounded])
  | intro x
  | split

/-- All outcomes of the ACTUAL row loop; no acceptance or domain premise. -/
theorem rows_bound (fuel : Nat) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    bounded fuel (Port9OR_P6Rows.rows fuel s physical i w) := by
  induction fuel generalizing s i w with
  | zero => simp only [Port9OR_P6Rows.rows]; split <;> simp only [liftResult,bounded] <;> trivial
  | succ fuel ih =>
    simp only [Port9OR_P6Rows.rows]
    split
    · trivial
    · have joined := bind_bound (Port9OR_P6Node.node s physical i w)
        (fun out => match out with
          | .Stop stopped => pure (.Stop stopped)
          | .Next next ni nw => Port9OR_P6Rows.rows fuel next physical ni nw) 1 fuel
        (node_bound s physical i w) (by
          intro out
          cases out with
          | Stop stopped => trivial
          | Next next ni nw => exact ih next ni nw)
      simpa only [Nat.add_comm] using joined

theorem leaf_bound (kind : Usize) (opening : Slice U8) :
    bounded 1 (Port4B_LeafCode.code kind opening) := by
  unfold Port4B_LeafCode.code Port4B_LeafCode.codeFor
  repeat' first
  | (solve | trivial)
  | (fail_if_no_progress simp only [bounded,liftResult])
  | intro x
  | constructor
  | split
  all_goals omega

/-- Concrete op8 emits three digest sites, on malformed as well as good state. -/
theorem writer_bound (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (proof pub : Slice U8) : bounded 3 (Port8EFF_Bodies.writerCode p a proof pub) := by
  simp only [Port8EFF_Bodies.writerCode,CheckpointBytes5Writer.writer,CheckpointBytes5Effect.bind,CheckpointBytes5Effect.read,bounded]
  exact ⟨by decide,fun _ => ⟨by decide,fun _ => ⟨by decide,fun _ => trivial⟩⟩⟩

theorem writer_count {X : Type} (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (proof pub : Slice U8) : (eval H (Port9OR_Bodies.writer D p a proof pub hash)).1.length≤3 :=
  count _ _ _ _ _ (writer_bound p a proof pub)

theorem rows_count {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (fuel : Nat) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    (eval H (Port9OR_Code.program D hash (Port9OR_P6Rows.rows fuel s physical i w))).1.length≤fuel :=
  count D hash _ H fuel (rows_bound fuel s physical i w)

#print axioms mono
#print axioms bind_bound
#print axioms parent_bound
#print axioms node_bound
#print axioms rows_bound
#print axioms leaf_bound
#print axioms writer_bound
#print axioms writer_count
#print axioms rows_count
end AspisR1.Port11PROV_SourceCount
end
