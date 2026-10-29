import PV_DIAG2_Termination
/-! Relevant-caller projections of source continuation stacks, separate from the actual PC list retained by
Execution. These source labels are never substituted for machine frames. -/
set_option autoImplicit false
namespace PV_DIAG2
inductive SourceFrame where
 | plan | resultMapErr | planErr | anyhowFormatErr | anyhowMsg | capture | prover | retry
 deriving DecidableEq, Repr

/-- A returned call resumes its saved continuation. Its complete effect
prefix (including any earlier captures) survives. Abnormal terminals keep
their actual panic/OOM PCs and never invoke the ordinary continuation. -/
def returnedCall {A B : Type} (body : Execution A) (saved : List SourceFrame)
    (continuation : A → List SourceFrame → Execution B) : Execution B :=
 bind body (fun value => continuation value saved)

def reportingSpine (outer : List SourceFrame) : List SourceFrame :=
 [.capture,.anyhowMsg,.anyhowFormatErr,.planErr,.resultMapErr,.plan] ++ outer

/-- No popped retry/prover source frame is added by this post-return path.
Any older frame in `outer` is preserved, not silently deleted. -/
theorem report_spine (outer : List SourceFrame) :
 reportingSpine outer = .capture :: .anyhowMsg :: .anyhowFormatErr :: .planErr :: .resultMapErr :: .plan :: outer := rfl

theorem return_resumes_saved {A B : Type} (a : A) (prior : List Effect)
    (outer : List SourceFrame) (next : A → List SourceFrame → Execution B) :
 returnedCall ⟨prior,.value a⟩ outer next = prepend prior (next a outer) := rfl

/-- Two different retry histories reach the same source continuation once
both have returned the same code. Their earlier diagnostic effects remain
independent prefixes; equality of those prefixes is not asserted. -/
theorem returned_error_spine (e : Error) (left right : List Effect)
    (outer : List SourceFrame) (report : Error → List SourceFrame → Execution Nat) :
 returnedCall ⟨left,.value e⟩ outer (fun e saved => report e (reportingSpine saved)) =
   prepend left (report e (reportingSpine outer)) ∧
 returnedCall ⟨right,.value e⟩ outer (fun e saved => report e (reportingSpine saved)) =
   prepend right (report e (reportingSpine outer)) := ⟨rfl,rfl⟩

theorem proving_panic_keeps_frames {A B : Type} (events : List Effect)
    (msg : String) (pcs : List Nat) (outer : List SourceFrame)
    (next : A → List SourceFrame → Execution B) :
 returnedCall ⟨events,.panic msg pcs⟩ outer next = ⟨events,.panic msg pcs⟩ := rfl

theorem proving_oom_keeps_frames {A B : Type} (events : List Effect)
    (size : Nat) (pcs : List Nat) (outer : List SourceFrame)
    (next : A → List SourceFrame → Execution B) :
 returnedCall ⟨events,.oom size pcs⟩ outer next = ⟨events,.oom size pcs⟩ := rfl

#print axioms report_spine
#print axioms return_resumes_saved
#print axioms returned_error_spine
#print axioms proving_panic_keeps_frames
#print axioms proving_oom_keeps_frames
end PV_DIAG2
