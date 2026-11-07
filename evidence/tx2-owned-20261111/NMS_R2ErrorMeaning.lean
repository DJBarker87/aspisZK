import NMS_R2Fold241
set_option autoImplicit false
namespace NMS_R2ErrorMeaning
open RSL RSL.TX2_241
/-- The actual source ordering of lib.rs::error: allocate the nonempty
format! String, then write its log, then return InvalidInstructionData.
Allocation failure carries no log and no returned error. -/
def error (V : V2Lib) (e : V.VErr) : RS Unit :=
 RS.seq (RS.lift Spec.alloc) <|
 RS.seq (RS.lift (Spec.emit (.log ("r1:error:" ++ V.debug e))))
  (RS.throw .invalidInstructionData)

theorem full (V : V2Lib) (e : V.VErr) : error V e = mapVErr V (.error e) := rfl

theorem abort (V : V2Lib) (e : V.VErr) (env : Env) :
 error V e env ⟨.abort,[]⟩ := by
 apply (RS.alloc_seq_iff _ env _).mpr
 exact Or.inr rfl

/-- Exact abort-prefix law at a caller occurrence. The prefix is retained
and there is no suffix log or post-abort returned value. -/
theorem prefixed_abort (V : V2Lib) (e : V.VErr) (env : Env) (preEvents : List Event) :
 ∃ suffix : Obs (Except ProgramError Unit), error V e env suffix ∧
  (⟨.abort,preEvents⟩ : Obs (Except ProgramError Unit)) =
   ⟨suffix.exit,preEvents ++ suffix.events⟩ := by
 exact ⟨⟨.abort,[]⟩,abort V e env,by simp⟩

/-- Returned verifier Ok never reaches the formatting allocation. -/
theorem ok (V : V2Lib) : mapVErr V (.ok ()) = RS.pure () := rfl
#print axioms full
#print axioms abort
#print axioms prefixed_abort
#print axioms ok
end NMS_R2ErrorMeaning
