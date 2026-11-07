import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMP_ObservedSteps (State execute body)
open NMT_CallTree (erase)
def f5 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges) :=
 c.c7 s.digest s.publicValue p t ch s.observer

def f4 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges) : Result (SemanticOut H) := do
 c.c8 s.observer 1#u8
 f5 c s p t ch

def f3 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) : Result (SemanticOut H) := do
 let (r,after) ← c.c5 s.digest p t
 match r with
 | .Err e => .ok (.Err e)
 | .Ok ch => f4 c s p after ch

def f2 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) : Result (SemanticOut H) := do
 let r ← c.c9 s.digest s.publicValue s.hash p.c1_root
 match r with
 | .Err e => .ok (.Err e)
 | .Ok t => f3 c s p t

def f1 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) : Result (SemanticOut H) := do
 c.c8 s.observer 0#u8
 f2 c s p

def f0 {H W : Type} (c : Calls) (s : Parent H W) : Result (SemanticOut H) := do
 let r ← c.c6 s.bytes
 match r with
 | .Err e => .ok (.Err e)
 | .Ok p => f1 c s p
end AspisR1.NMP_ObservedSuffix
