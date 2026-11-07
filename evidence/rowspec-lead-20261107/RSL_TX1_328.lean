/-
TX1:328  programs/r1-cost-probe/src/lib.rs::first_decoded
Frozen signature (lib.rs:49):
  fn first_decoded(public: aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,
      public_bytes: &[u8], proof: &[u8], k: usize) -> Result<Vec<u8>, ProgramError>
  body: verifier::tx1(public, public_bytes, proof, k, SolanaDigest, observer()).map_err(error)
Route: emitted body under (bm).
Children: OPEN tx1 TX1:094 (RowSpec_094 reference at SAME arguments, with
obs = observer() = None from CLOSED TX1:329, which discharges (T1)); CLOSED
lib.rs::error (TX1:NGB001: one log line `r1:error:{:?}` then
InvalidInstructionData).
Own-input domain ((bf)(2)), caller clause of TX1:345: V.publicDom public.
Effects: tx1's ordered events; on Err one log line after them.
-/
import RSL_TX1_094
set_option autoImplicit false

namespace RSL.TX1_328

abbrev Args (V : VLib) := TX1_094.Args V

/-- `.map_err(error)` (lib.rs:40). -/
def mapVErr (V : VLib) (r : Except V.VErr Bytes) : RS Bytes :=
  match r with
  | .ok b => RS.pure b
  | .error e => RS.seq (RS.lift (Spec.emit (.log ("r1:error:" ++ V.debugV e))))
                  (RS.throw .invalidInstructionData)

def Ref (V : VLib) (P : PreparedNew V) (a : Args V) : RS Bytes :=
  Spec.bind (Spec.call (fun x : Args V => TX1_094.Domain V x none x.public_) (TX1_094.Ref V P) a)
    (mapVErr V)

def Domain (V : VLib) (a : Args V) : Prop := V.publicDom a.public_

def RowSpec_328 (V : VLib) (P : PreparedNew V)
    (first_decoded : Args V → Env → Obs (Except ProgramError Bytes)) : Prop :=
  ∀ a env, Domain V a → Ref V P a env (first_decoded a env)

/-! ## Rejection of trivial implementations: at k ≠ 10 the reference forces
exactly one log line followed by Err(InvalidInstructionData); a silent
constant Err (no events) or a constant abort is therefore rejected. -/

theorem rejects_silent (V : VLib) (P : PreparedNew V) (a : Args V) (hk : a.k ≠ SPLIT)
    (hd : Domain V a) (r : Exit (Except ProgramError Bytes)) :
    ¬ RowSpec_328 V P (fun _ _ => ⟨r, []⟩) := by
  intro h
  have h1 := h a env0 hd
  unfold Ref at h1
  have h094 : ∀ o, Spec.call (fun x : Args V => TX1_094.Domain V x none x.public_) (TX1_094.Ref V P)
      a env0 o ↔ o = ⟨.ret (.error V.vParse), []⟩ := by
    intro o
    rw [Spec.call_trivial _ _ _ ⟨rfl, hd⟩]
    unfold TX1_094.Ref
    have c : (a.k != SPLIT) = true := by simp [hk]
    rw [c, RE.check_true, RE.seq_throw]
    rfl
  rw [Spec.bind_det _ _ env0 _ h094] at h1
  unfold mapVErr RS.seq RS.bind RS.lift Spec.map at h1
  rcases h1 with ⟨x, e1, o2, hm, _, ho⟩ | ⟨e1, hm, ho⟩ | ⟨e1, hm, ho⟩
  · rcases hm with ⟨u, e0, o0, ha, _, hm⟩ | ⟨_, ha, _⟩ | ⟨_, ha, _⟩
    · simp only [Spec.emit, Obs.mk.injEq] at ha
      rcases ha with ⟨_, rfl⟩
      simp only [Obs.mk.injEq] at hm ho
      rw [hm.2] at ho
      simp at ho
    · simp [Spec.emit] at ha
    · simp [Spec.emit] at ha
  · rcases hm with ⟨u, e0, o0, ha, hp, hm⟩ | ⟨_, ha, _⟩ | ⟨_, ha, _⟩
    · simp only [Spec.pure] at hp; subst hp; simp at hm
    · simp [Spec.emit] at ha
    · simp [Spec.emit] at ha
  · rcases hm with ⟨u, e0, o0, ha, hp, hm⟩ | ⟨_, ha, _⟩ | ⟨_, ha, _⟩
    · simp only [Spec.pure] at hp; subst hp; simp at hm
    · simp [Spec.emit] at ha
    · simp [Spec.emit] at ha

end RSL.TX1_328
