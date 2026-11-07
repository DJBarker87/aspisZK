from pathlib import Path
E=Path(__file__).resolve().parent
header='''import NMP_EmittedContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
'''
text=header+'''/-- One typed parent state, six source-order call occurrences. All original
arguments/world remain in Parent. Complete outer stopped results are in Code,
so they acquire neither suffix calls nor a final world. -/
inductive State (H W : Type) where
 | parse (s : Parent H W)
 | mark0 (s : Parent H W) (p : r1_wire.Prefix)
 | publicTranscript (s : Parent H W) (p : r1_wire.Prefix)
 | begin_ (s : Parent H W) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
 | mark1 (s : Parent H W) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
     (ch : aspis_core.state_only_prefix.r0.Challenges)
 | finish (s : Parent H W) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
     (ch : aspis_core.state_only_prefix.r0.Challenges)

def step {H W : Type} (c : Calls) : State H W → Code (Sum (SemanticOut H) (State H W))
 | .parse s => do
   let r ← invoke "TX1:138/parse" s.bytes (c.c6 s.bytes)
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok p => pure (.inr (.mark0 s p))
 | .mark0 s p => do
   let _ ← invoke "TX1:130/mark0" (s.observer,0#u8) (c.c8 s.observer 0#u8)
   pure (.inr (.publicTranscript s p))
 | .publicTranscript s p => do
   let r ← invoke "TX1:131/public_transcript" (s.publicValue,s.hash,p.c1_root)
     (c.c9 s.digest s.publicValue s.hash p.c1_root)
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok t => pure (.inr (.begin_ s p t))
 | .begin_ s p t => do
   let (r,after) ← invoke "TX1:150/begin" (p,t) (c.c5 s.digest p t)
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok ch => pure (.inr (.mark1 s p after ch))
 | .mark1 s p t ch => do
   let _ ← invoke "TX1:130/mark1" (s.observer,1#u8) (c.c8 s.observer 1#u8)
   pure (.inr (.finish s p t ch))
 | .finish s p t ch => do
   let r ← invoke "TX1:136/verify_finish" (s.publicValue,p,t,ch,s.observer)
     (c.c7 s.digest s.publicValue p t ch s.observer)
   pure (.inl r)

def execute {H W : Type} (c : Calls) : Nat → State H W → Code (SemanticOut H)
 | 0,_ => .plain (.fail .panic) .done
 | n+1,s => do
   let r ← step c s
   match r with
   | .inl out => pure out
   | .inr next => execute c n next

def body {H W : Type} (c : Calls) (s : Parent H W) := execute c 6 (.parse s)
end AspisR1.NMP_ObservedSteps
'''
(E/'NMP_ObservedState.lean').write_text(text)
# Source-order occurrences expose the SAME typed arguments and full replies.
for i,(name,args,st,rhs) in enumerate([
 ('parse','', '.parse s','''(do let r ← invoke "TX1:138/parse" s.bytes (c.c6 s.bytes)
      match r with
      | .Err e => pure (.inl (.Err e))
      | .Ok p => pure (.inr (.mark0 s p)))'''),
 ('mark0','(p : r1_wire.Prefix)', '.mark0 s p','''(do let _ ← invoke "TX1:130/mark0" (s.observer,0#u8) (c.c8 s.observer 0#u8)
      pure (.inr (.publicTranscript s p)))'''),
 ('publicTranscript','(p : r1_wire.Prefix)', '.publicTranscript s p','''(do let r ← invoke "TX1:131/public_transcript" (s.publicValue,s.hash,p.c1_root) (c.c9 s.digest s.publicValue s.hash p.c1_root)
      match r with
      | .Err e => pure (.inl (.Err e))
      | .Ok t => pure (.inr (.begin_ s p t)))'''),
 ('begin_','(p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)', '.begin_ s p t','''(do let (r,after) ← invoke "TX1:150/begin" (p,t) (c.c5 s.digest p t)
      match r with
      | .Err e => pure (.inl (.Err e))
      | .Ok ch => pure (.inr (.mark1 s p after ch)))'''),
 ('mark1','(p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges)', '.mark1 s p t ch','''(do let _ ← invoke "TX1:130/mark1" (s.observer,1#u8) (c.c8 s.observer 1#u8)
      pure (.inr (.finish s p t ch)))'''),
 ('finish','(p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges)', '.finish s p t ch','''(do let r ← invoke "TX1:136/verify_finish" (s.publicValue,p,t,ch,s.observer) (c.c7 s.digest s.publicValue p t ch s.observer)
      pure (.inl r))''')]):
 rhs=rhs.replace('(do let','(do\n      let')
 module='NMP_ObservedStep'+str(i)
 text=header.replace('import NMP_EmittedContext','import NMP_ObservedState')+f'''/-- Occurrence {i}, {name}; exact full typed call, no callee-law premise. -/
theorem occurrence{i} {{H W : Type}} (c : Calls) (s : Parent H W) {args} :
 step c ({st}) = {rhs} := rfl
#print axioms occurrence{i}
end AspisR1.NMP_ObservedSteps
'''
 (E/(module+'.lean')).write_text(text)
print('Drafted one state and six source-order occurrence modules')
