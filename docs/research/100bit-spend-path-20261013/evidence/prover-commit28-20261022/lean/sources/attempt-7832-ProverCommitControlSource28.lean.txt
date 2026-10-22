import R1Z.ProverCommitControlProgram28
/-! Kernel-checked reconstruction of the retained source from the generic
monadic continuation. This checks the complete pure instruction schedule. -/
set_option autoImplicit false
namespace R1Z.ProverCommitControlSource28
open Aeneas Aeneas.Std Result AspisR1SimControl21

variable {H P : Type} (hash : aspis_core.digest.Digest32 H)
  (policy : transcript.control21.Policy P)
  (s : transcript.control21.Transcript H P) (row : U8) (payload : Slice U8)

theorem absorb : transcript.control21.Transcript.absorb hash policy s row payload =
    ProverCommitControlProgram28.absorb hash.digest policy s row payload := by rfl

theorem queries : transcript.control21.Transcript.queries hash policy s row payload =
    ProverCommitControlProgram28.queries hash.digest policy s row payload := by
  unfold transcript.control21.Transcript.queries ProverCommitControlProgram28.queries
  rw [absorb hash policy s row payload]
  repeat
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro v hv
    try dsimp only [Aeneas.Std.uncurry]
  rfl

theorem block : transcript.control21.Transcript.block hash policy s row payload =
    ProverCommitControlProgram28.block hash.digest policy s row payload := by rfl

theorem scalar (nonzero : Bool) :
    transcript.control21.Transcript.scalar hash policy s row payload nonzero =
    ProverCommitControlProgram28.scalar hash.digest policy s row payload nonzero := by rfl

theorem scalar_k : transcript.control21.Transcript.scalar_k hash policy s row payload =
    ProverCommitControlProgram28.scalar_k hash.digest policy s row payload := by rfl

theorem start (token : H) (state : Array U8 32#usize) (variant : transport.Variant) :
    transcript.control21.Transcript.new hash policy token state variant =
    ProverCommitControlProgram28.start hash.digest policy token state variant := by rfl

theorem tail (token : H) (state : Array U8 32#usize)
    (sem : Array aspis_core.field.QM31 25#usize)
    (z : Array (Array aspis_core.field.QM31 2#usize) 2#usize)
    (records : sim.Records) (variant : transport.Variant) :
    sim.tail_control21 hash policy token state sem z records variant =
    ProverCommitControlProgram28.tail hash.digest policy token state sem z records variant := by
  simp only [sim.tail_control21,ProverCommitControlProgram28.tail,
    ← start,← scalar,← queries,← scalar_k]
  rfl

#print axioms absorb
#print axioms queries
#print axioms block
#print axioms scalar
#print axioms scalar_k
#print axioms start
#print axioms tail
end R1Z.ProverCommitControlSource28
