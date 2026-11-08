import NNG_Context137
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Tree137
open Aeneas Aeneas.Std Result NMP_prepare NNG_Context137 NMT_CallTree

def finish {H : Type} (c : Calls) (s : Parent H) (p : r1_wire.Prefix)
    (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges) : Code (Output H) :=
  invoke "TX1:136/verify_finish" (s.publicValue,p,t,ch,s.observer) (c.finish s.digest s.publicValue p t ch s.observer)
def mark1 {H : Type} (c : Calls) (s : Parent H) (p : r1_wire.Prefix)
    (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges) : Code (Output H) := do
  invoke "TX1:130/mark1" (s.observer,1#u8) (c.mark s.observer 1#u8)
  finish c s p t ch
def begin_ {H : Type} (c : Calls) (s : Parent H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) : Code (Output H) := do
  let (reply,after)←invoke "TX1:150/begin" (p,t) (c.begin_ s.digest p t)
  match reply with
  | .Err e=>pure (.Err e)
  | .Ok ch=>mark1 c s p after ch
def publicTranscript {H : Type} (c : Calls) (s : Parent H) (p : r1_wire.Prefix) : Code (Output H) := do
  let reply←invoke "TX1:131/public_transcript" (s.publicValue,s.hash,p.c1_root) (c.publicTranscript s.digest s.publicValue s.hash p.c1_root)
  match reply with
  | .Err e=>pure (.Err e)
  | .Ok t=>begin_ c s p t
def mark0 {H : Type} (c : Calls) (s : Parent H) (p : r1_wire.Prefix) : Code (Output H) := do
  invoke "TX1:130/mark0" (s.observer,0#u8) (c.mark s.observer 0#u8)
  publicTranscript c s p
def tree {H : Type} (c : Calls) (s : Parent H) : Code (Output H) := do
  let reply←invoke "TX1:138/parse" s.bytes (c.parse s.bytes)
  match reply with
  | .Err e=>pure (.Err e)
  | .Ok p=>mark0 c s p
end AspisR1.NNG_Tree137
