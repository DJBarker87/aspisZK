import Init

/-! Diagnostic carrier: effects survive every terminal case. A frame is an
opaque machine observation, never replaced by an environment-enable bit.
This is an instrumentation specification, not an implementation assumption. -/
set_option autoImplicit false
namespace PV_DIAG2
inductive Error where
 | Parse | Semantic | Transcript | Relation | Merkle | Query | Checkpoint
 | Allocation | Rejected | AttemptsExhausted | Entropy
 deriving DecidableEq, Repr

def spelling : Error → String
 | .Parse => "Parse"
 | .Semantic => "Semantic"
 | .Transcript => "Transcript"
 | .Relation => "Relation"
 | .Merkle => "Merkle"
 | .Query => "Query"
 | .Checkpoint => "Checkpoint"
 | .Allocation => "Allocation"
 | .Rejected => "Rejected"
 | .AttemptsExhausted => "AttemptsExhausted"
 | .Entropy => "Entropy"

inductive Effect where
 | stdout : String → Effect
 | stderr : String → Effect
 | returned : Error → Effect
 | capture : List Nat → Effect
 | panic : String → List Nat → Effect
 | oom : Nat → List Nat → Effect
 | foreign : String → List Nat → Effect
 deriving DecidableEq, Repr

inductive Terminal (A : Type) where
 | value : A → Terminal A
 | panic : String → List Nat → Terminal A
 | oom : Nat → List Nat → Terminal A
 | diverge : Terminal A
 deriving Repr

structure Execution (A : Type) where
 effects : List Effect
 terminal : Terminal A
 deriving Repr

def prepend {A : Type} (prior : List Effect) (x : Execution A) : Execution A :=
 ⟨prior ++ x.effects, x.terminal⟩

def bind {A B : Type} (x : Execution A) (f : A → Execution B) : Execution B :=
 match x.terminal with
 | .value a => prepend x.effects (f a)
 | .panic msg pcs => ⟨x.effects, .panic msg pcs⟩
 | .oom size pcs => ⟨x.effects, .oom size pcs⟩
 | .diverge => ⟨x.effects, .diverge⟩

/-- `stderr` records the requested formatted write; partial/failed I/O is a
separate native effect, not a guarantee that these bytes are delivered.
Ordinary anyhow Debug can append a trace. Keep that suffix as an input
requiring its own law; do not pretend the unit variant determines frames. -/
def reportError (e : Error) (frames : List Nat) (renderedTrace : String)
    (captureEnabled : Bool) : Execution Nat :=
 ⟨(if captureEnabled then [.capture frames] else []) ++ [.returned e] ++
   [.stderr ("Error: " ++ spelling e ++ renderedTrace ++ "\n")], .value 1⟩

/-- Unit-variant content has no witness operand. Occurrence and frames are
separate obligations, represented by separate arguments above. -/
theorem message_public (left right : Error) (sameVariant : left = right) :
 spelling left = spelling right := congrArg spelling sameVariant

theorem report_disabled (e : Error) (frames : List Nat) :
 reportError e frames "" false =
 ⟨[.returned e, .stderr ("Error: " ++ spelling e ++ "\n")], .value 1⟩ := by
 simp [reportError]

theorem disabled_frames_irrelevant (e : Error) (a b : List Nat) :
 reportError e a "" false = reportError e b "" false := by
 rw [report_disabled, report_disabled]

/-- The returned-error formatter/report stage contributes no events to an
already successful main result. Effects produced before main are retained. -/
def terminate (result : Except Error Unit) (frames : List Nat) (suffix : String)
    (enabled : Bool) : Execution Nat :=
 match result with
 | .ok () => ⟨[], .value 0⟩
 | .error e => reportError e frames suffix enabled

theorem success_report_silent (frames : List Nat) (suffix : String) (enabled : Bool) :
 (terminate (.ok ()) frames suffix enabled).effects = [] := rfl

theorem error_report_exact (e : Error) (frames : List Nat) :
 terminate (.error e) frames "" false =
 ⟨[.returned e, .stderr ("Error: " ++ spelling e ++ "\n")], .value 1⟩ :=
 report_disabled e frames

/-- No successful-return premise is silently used for panic or OOM. -/
theorem bind_panic {A B : Type} (events : List Effect) (msg : String) (pcs : List Nat)
    (f : A → Execution B) :
 bind ⟨events, .panic msg pcs⟩ f = ⟨events, .panic msg pcs⟩ := rfl

theorem bind_oom {A B : Type} (events : List Effect) (size : Nat) (pcs : List Nat)
    (f : A → Execution B) :
 bind ⟨events, .oom size pcs⟩ f = ⟨events, .oom size pcs⟩ := rfl

/-- A pre-existing effect is retained when a later operation panics. -/
theorem prior_panic {A : Type} (prior tail : List Effect) (msg : String) (pcs : List Nat) :
 prepend prior (⟨tail, .panic msg pcs⟩ : Execution A) =
 ⟨prior ++ tail, .panic msg pcs⟩ := rfl

#print axioms message_public
#print axioms report_disabled
#print axioms disabled_frames_irrelevant
#print axioms success_report_silent
#print axioms error_report_exact
#print axioms bind_panic
#print axioms bind_oom
#print axioms prior_panic
end PV_DIAG2
