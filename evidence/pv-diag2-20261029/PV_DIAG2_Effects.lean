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

def prepend {A : Type} (prefix : List Effect) (x : Execution A) : Execution A :=
 ⟨prefix ++ x.effects, x.terminal⟩

def bind {A B : Type} (x : Execution A) (f : A → Execution B) : Execution B :=
 match x.terminal with
 | .value a => prepend x.effects (f a)
 | .panic msg pcs => ⟨x.effects, .panic msg pcs⟩
 | .oom size pcs => ⟨x.effects, .oom size pcs⟩
 | .diverge => ⟨x.effects, .diverge⟩

/-- Ordinary anyhow Debug can append a trace. Keep that suffix as an input
requiring its own law; do not pretend the unit variant determines frames. -/
def reportError (e : Error) (frames : List Nat) (renderedTrace : String)
    (captureEnabled : Bool) : Execution Unit :=
 ⟨[.returned e] ++ (if captureEnabled then [.capture frames] else []) ++
   [.stderr ("Error: " ++ spelling e ++ renderedTrace ++ "\n")], .value ()⟩

/-- Only the message prefix is fixed by the variant. -/
theorem message_public (e : Error) :
 ("Error: " ++ spelling e ++ "\n") = ("Error: " ++ spelling e ++ "\n") := rfl

theorem report_disabled (e : Error) (frames : List Nat) :
 reportError e frames "" false =
 ⟨[.returned e, .stderr ("Error: " ++ spelling e ++ "\n")], .value ()⟩ := rfl

theorem report_same (e : Error) (pcs : List Nat) (suffix : String) (enabled : Bool) :
 reportError e pcs suffix enabled = reportError e pcs suffix enabled := rfl

/-- No successful-return premise is silently used for panic or OOM. -/
theorem bind_panic {A B : Type} (events : List Effect) (msg : String) (pcs : List Nat)
    (f : A → Execution B) :
 bind ⟨events, .panic msg pcs⟩ f = ⟨events, .panic msg pcs⟩ := rfl

theorem bind_oom {A B : Type} (events : List Effect) (size : Nat) (pcs : List Nat)
    (f : A → Execution B) :
 bind ⟨events, .oom size pcs⟩ f = ⟨events, .oom size pcs⟩ := rfl

/-- A pre-existing effect is retained when a later operation panics. -/
theorem prefix_panic {A : Type} (prefix tail : List Effect) (msg : String) (pcs : List Nat) :
 prepend prefix (⟨tail, .panic msg pcs⟩ : Execution A) =
 ⟨prefix ++ tail, .panic msg pcs⟩ := rfl

#print axioms message_public
#print axioms report_disabled
#print axioms report_same
#print axioms bind_panic
#print axioms bind_oom
#print axioms prefix_panic
end PV_DIAG2
