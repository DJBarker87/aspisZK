/-
TX1:328  programs/r1-cost-probe/src/lib.rs::first_decoded
Frozen signature (lib.rs:49):
  fn first_decoded(public: aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,
      public_bytes: &[u8], proof: &[u8], k: usize) -> Result<Vec<u8>, ProgramError>
  body: verifier::tx1(public, public_bytes, proof, k, SolanaDigest, observer()).map_err(error)
Route: emitted body under (bm).
Children: OPEN tx1 TX1:094 (RowSpec_094 reference at SAME arguments, with
obs = observer() = None from CLOSED TX1:329, which discharges (T1)); CLOSED
lib.rs::error (TX1:NGB001: the `format!` allocation, one log line
`r1:error:{:?}`, then InvalidInstructionData; the allocation site is Revision 2).
Own-input domain ((bf)(2)), caller clause of TX1:345: V.publicDom public.
Effects: tx1's ordered events; on Err one log line after them.
-/
import NMT_RSL_TX1_094
import NMT_R2_Base
set_option autoImplicit false

namespace NMT_R2.TX1_328
open RSL

abbrev Args (V : VLib) := TX1_094.Args V

/-- `.map_err(error)` (lib.rs:40): `msg!("r1:error:{:?}", e)` expands to
`sol_log(&format!(..))`; Revision 2 adds the `format!` String allocation site
before the log line (abort = prefix so far). -/
def mapVErr (V : VLib) (r : Except V.VErr Bytes) : RS Bytes :=
  match r with
  | .ok b => RS.pure b
  | .error e => RS.seq (RS.lift Spec.alloc) <|   -- format! builds the message String
               RS.seq (RS.lift (Spec.emit (.log ("r1:error:" ++ V.debugV e))))
                  (RS.throw .invalidInstructionData)

def Ref (V : VLib) (P : PreparedNew V) (a : Args V) : RS Bytes :=
  Spec.bind (Spec.call (fun x : Args V => TX1_094.Domain V x none x.public_) (TX1_094.Ref V P) a)
    (mapVErr V)

def Domain (V : VLib) (a : Args V) : Prop := V.publicDom a.public_

def RowSpec_328 (V : VLib) (P : PreparedNew V)
    (first_decoded : Args V → Env → Obs (Except ProgramError Bytes)) : Prop :=
  ∀ a env, Domain V a → Ref V P a env (first_decoded a env)

/-! ## Rejection of trivial implementations (Revision 2)

At k ≠ 10 tx1 returns Err(Parse) with no event; `error` then builds its message
with `format!` (an allocation site) and logs it.  The reference therefore admits
exactly the log line followed by Err(InvalidInstructionData), or the silent
allocation abort.  Every event-free RETURNING implementation (in particular every
constant Err) is rejected (`rejects_silentRet`).

The Revision 1 theorem `rejects_silent` also rejected the constant abort.  That
was an artefact of omitting the `format!` allocation: the frozen function can
abort with an empty prefix at that site, so the faithful reference admits it
(`ref_admits_abort`).  Revision 2 withdraws that part of the claim and records
the reason in RSL_REVISION2.md. -/

theorem ref_k_det (V : VLib) (P : PreparedNew V) (a : Args V) (hk : a.k ≠ SPLIT)
    (hd : Domain V a) (o : Obs (Except V.VErr Bytes)) :
    Spec.call (fun x : Args V => TX1_094.Domain V x none x.public_) (TX1_094.Ref V P)
      a env0 o ↔ o = ⟨.ret (.error V.vParse), []⟩ := by
  rw [Spec.call_trivial _ _ _ ⟨rfl, hd⟩]
  unfold TX1_094.Ref
  have c : (a.k != SPLIT) = true := by simp [hk]
  rw [c, RE.check_true, RE.seq_throw]
  rfl

theorem rejects_silentRet (V : VLib) (P : PreparedNew V) (a : Args V) (hk : a.k ≠ SPLIT)
    (hd : Domain V a) (x : Except ProgramError Bytes) :
    ¬ RowSpec_328 V P (fun _ _ => ⟨.ret x, []⟩) := by
  intro h
  have h1 := h a env0 hd
  unfold Ref at h1
  rw [Spec.bind_det _ _ env0 _ (ref_k_det V P a hk hd)] at h1
  unfold mapVErr at h1
  rcases (RS.alloc_seq_iff _ env0 _).mp h1 with h2 | h2
  · unfold RS.seq RS.bind at h2
    have := Spec.bind_nonempty _ _ _ _ (fun o' h' => by
      unfold RS.lift Spec.map at h'
      exact Spec.emit_bind_nonempty _ _ _ _ h') h2
    exact this rfl
  · simp at h2

theorem ref_admits_abort (V : VLib) (P : PreparedNew V) (a : Args V) (hk : a.k ≠ SPLIT)
    (hd : Domain V a) : Ref V P a env0 ⟨.abort, []⟩ := by
  unfold Ref
  rw [Spec.bind_det _ _ env0 _ (ref_k_det V P a hk hd)]
  unfold mapVErr
  exact (RS.alloc_seq_iff _ env0 _).mpr (Or.inr rfl)

end NMT_R2.TX1_328
