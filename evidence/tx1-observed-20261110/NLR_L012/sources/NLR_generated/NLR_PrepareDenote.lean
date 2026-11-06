import NLR_PrepareTails
import NLC_LeafSound
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
def rank {H : Type} (s : State H) : Nat :=
 match s.locals with
 | .allocate  => 12
 | .split _ _ => 11
 | .semanticRange _ _ _ _ _ => 10
 | .expandSemantic _ _ _ _ _ _ _ => 9
 | .valueRange _ _ _ _ _ _ => 8
 | .expandValues _ _ _ _ _ _ => 7
 | .rebuild _ _ _ _ _ => 6
 | .view _ _ _ => 5
 | .semantic _ _ => 4
 | .mapSemantic _ _ _ => 3
 | .mark _ _ _ => 2
 | .constructor _ _ _ => 1
def denote (cfg : Configuration) {H : Type} (s : State H) : Code Out :=
 match s.locals with
 | .allocate  => NLR_PrepareTails.tail_allocate cfg s.input 
 | .split n logical => NLR_PrepareTails.tail_split cfg s.input n logical
 | .semanticRange n semantic y1 splitBack vecBack => NLR_PrepareTails.tail_semanticRange cfg s.input n semantic y1 splitBack vecBack
 | .expandSemantic n offY1 semantic y1 compressed splitBack vecBack => NLR_PrepareTails.tail_expandSemantic cfg s.input n offY1 semantic y1 compressed splitBack vecBack
 | .valueRange n offY1 semantic y1 splitBack vecBack => NLR_PrepareTails.tail_valueRange cfg s.input n offY1 semantic y1 splitBack vecBack
 | .expandValues n semantic y1 compressed splitBack vecBack => NLR_PrepareTails.tail_expandValues cfg s.input n semantic y1 compressed splitBack vecBack
 | .rebuild n semantic y1 splitBack vecBack => NLR_PrepareTails.tail_rebuild cfg s.input n semantic y1 splitBack vecBack
 | .view logical semantic y1 => NLR_PrepareTails.tail_view cfg s.input logical semantic y1
 | .semantic logical v => NLR_PrepareTails.tail_semantic cfg s.input logical v
 | .mapSemantic logical v r => NLR_PrepareTails.tail_mapSemantic cfg s.input logical v r
 | .mark logical v sem => NLR_PrepareTails.tail_mark cfg s.input logical v sem
 | .constructor logical v sem => NLR_PrepareTails.tail_constructor cfg s.input logical v sem
def continuation (cfg : Configuration) {H : Type} : Post H → Code Out
 | .inl out => pure out
 | .inr after => denote cfg after

def FramePost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True | .inr after => after.input=s.input

def ProgressPost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True | .inr after => rank after < rank s
end AspisR1.NLR_Prepare
end
