import ExtractedOpeningCalls
import ExtractedOpeningQueriesReachability
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.OpeningRun
open r1_wire

def bindQueries (B : PreparedModel.Boundaries) (Q : QueriesModel.Boundaries) :
    PreparedModel.Boundaries :=
  { B with queries := fun D self row payload => QueriesModel.queries Q D self row payload }

/-- Each node is an actual current source call with its returned state. -/
inductive Run {H : Type} (Q : QueriesModel.Boundaries) (D : aspis_core.Digest32 H) :
    transcript.Transcript H → List U8 → transcript.Transcript H → Prop
  | nil (self) : Run Q D self [] self
  | scalar {self mid after row rows payload block}
      (call : transcript.Transcript.block D self row payload = ok (block,mid))
      (tail : Run Q D mid rows after) : Run Q D self (row::rows) after
  | queries {self mid after row rows payload output}
      (call : QueriesModel.queries Q D self row payload = ok (.Ok output,mid))
      (tail : Run Q D mid rows after) : Run Q D self (row::rows) after

theorem block_hash {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize)
    (h : transcript.Transcript.block D self row payload = ok (block,after)) :
    after.hash = self.hash := by
  obtain ⟨absorbed,state,ha,_,_,he⟩ := CallerStep.opening_block_success D self after row payload block h
  rw [he]
  exact OpeningCalls.absorb_hash D self absorbed row payload ha

theorem queries_hash {H : Type} (Q : QueriesModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (output : Array U32 22#usize)
    (h : QueriesModel.queries Q D self row payload = ok (.Ok output,after)) :
    after.hash = self.hash := by
  obtain ⟨absorbed,blocks,advances,selected,ha,_,he⟩ :=
    QueriesCalls.queries_success Q D self after row payload output h
  rw [he]
  exact OpeningCalls.absorb_hash D self absorbed row payload ha

theorem Run.hash {H : Type} {Q : QueriesModel.Boundaries} {D : aspis_core.Digest32 H}
    {self after : transcript.Transcript H} {rows : List U8} (run : Run Q D self rows after) :
    after.hash = self.hash := by
  induction run with
  | nil => rfl
  | scalar call tail ih => exact ih.trans (block_hash D _ _ _ _ _ call)
  | queries call tail ih => exact ih.trans (queries_hash Q D _ _ _ _ _ call)

/-- The actual Prepared success reaches all six opening rows on the two-fold
path (five on S1), including the actual query implementation and final rho.
The scalar arithmetic and query decoder/embedding remain explicit parameters. -/
theorem prepare_run {H : Type} (B : PreparedModel.Boundaries) (Q : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (view : verifier.View)
    (hash : H) (out : verifier.Prepared)
    (h : PreparedModel.prepare (bindQueries B Q) D sem view hash = ok (.Ok out)) :
    ∃ start last,
      transcript.Transcript.new D hash sem.transcript.state view.variant = ok start ∧
      out.state = last.state ∧
      ((transport.Variant.folds view.variant = ok 1#usize ∧
          Run Q D start [27#u8,28#u8,29#u8,30#u8,31#u8] last) ∨
       (transport.Variant.folds view.variant = ok 2#usize ∧
          Run Q D start [27#u8,28#u8,29#u8,30#u8,31#u8,32#u8] last)) := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha,hseed,hgamma,hbytes,hkappa,halpha,tail⟩ :=
    PreparedReachability.prepare_success (bindQueries B Q) D sem view hash out h
  obtain ⟨b0,hb0,_⟩ := OpeningCalls.scalar_success (bindQueries B Q) D _ _ _ _ _ _ hgamma
  obtain ⟨b1,hb1,_⟩ := OpeningCalls.scalar_success (bindQueries B Q) D _ _ _ _ _ _ hkappa
  obtain ⟨b2,hb2,_⟩ := OpeningCalls.scalar_success (bindQueries B Q) D _ _ _ _ _ _ halpha
  cases tail with
  | single hfolds tail =>
    obtain ⟨output,t4,last,rho,claim,hqueries,hrho,hclaim,hout⟩ := tail
    obtain ⟨brho,hbrho,_⟩ := OpeningCalls.rho_success (bindQueries B Q) D _ _ _ _ _ hrho
    refine ⟨start,last,hseed,?_,Or.inl ⟨hfolds,?_⟩⟩
    · rw [hout]; rfl
    · exact Run.scalar hb0 (Run.scalar hb1 (Run.scalar hb2
        (Run.queries hqueries (Run.scalar hbrho (Run.nil last)))))
  | double hfolds root bytes1 bytes2 alpha1 t4 hroot hb1copy hb2copy halpha1 tail =>
    obtain ⟨b3,hb3,_⟩ := OpeningCalls.scalar_success (bindQueries B Q) D _ _ _ _ _ _ halpha1
    obtain ⟨output,t5,last,rho,claim,hqueries,hrho,hclaim,hout⟩ := tail
    obtain ⟨brho,hbrho,_⟩ := OpeningCalls.rho_success (bindQueries B Q) D _ _ _ _ _ hrho
    refine ⟨start,last,hseed,?_,Or.inr ⟨hfolds,?_⟩⟩
    · rw [hout]; rfl
    · exact Run.scalar hb0 (Run.scalar hb1 (Run.scalar hb2 (Run.scalar hb3
        (Run.queries hqueries (Run.scalar hbrho (Run.nil last))))))
#print axioms block_hash
#print axioms queries_hash
#print axioms Run.hash
#print axioms prepare_run
end AspisR1PublicPreparation.OpeningRun
