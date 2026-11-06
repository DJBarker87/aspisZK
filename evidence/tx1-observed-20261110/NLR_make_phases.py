from pathlib import Path
import re
P=Path(__file__).resolve().parent/'NLR_generated'
phases=['allocate','split','semanticRange','expandSemantic','valueRange','expandValues','rebuild','view','semantic','mapSemantic','mark','constructor']
header='''set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
'''
params={};args={}
for phase in phases:
 src=Path(f'evidence/tx1-prepare-20261110/NLJ_generated/NLJ_PrepareWindow_{phase}.lean').read_text()
 signature=src.split(' : Code (Post H) := do')[0].split('def window_'+phase)[1]
 params[phase]=signature
 args[phase]=re.search(r'\(atSite : s.locals = \.'+phase+r'(.*?)\) :',src,re.S).group(1).strip()
rank='import NLR_PrepareTails\nimport NLC_LeafSound\n'+header
rank+='def rank {H : Type} (s : State H) : Nat :=\n match s.locals with\n'
for j,phase in enumerate(phases): rank+=' | .'+phase+' '+(' '.join('_' for _ in args[phase].split()))+' => '+str(12-j)+'\n'
rank+='def denote (cfg : Configuration) {H : Type} (s : State H) : Code Out :=\n match s.locals with\n'
for phase in phases:rank+=' | .'+phase+' '+args[phase]+' => NLR_PrepareTails.tail_'+phase+' cfg s.input '+args[phase]+'\n'
rank+='''def continuation (cfg : Configuration) {H : Type} : Post H → Code Out
 | .inl out => pure out
 | .inr after => denote cfg after

def FramePost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True | .inr after => after.input=s.input

def ProgressPost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True | .inr after => rank after < rank s
end AspisR1.NLR_Prepare
end
'''
(P/'NLR_PrepareDenote.lean').write_text(rank)
for phase in phases:
 par=params[phase];a=args[phase];at=f'(atSite : s.locals = .{phase} {a})'
 for kind in ['Frame','Progress']:
  k=kind.lower();prop=kind+'Post'
  txt=f'import NLR_PrepareDenote\nimport NLJ_PrepareWindow_{phase}\n'+header
  txt+=f'theorem {k}_{phase} {par}\n {at} : NLC_Finish.AllLeaves ({prop} s) (step cfg s) := by\n'
  txt+=f' rw [step_{phase} cfg s '+a+' atSite]\n'+f' unfold window_{phase}\n'
  txt+=''' repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
'''
  if kind=='Frame':txt+=' all_goals rfl\n'
  else:txt+=' all_goals change rank _ < rank s\n all_goals simp only [rank,advance,atSite]\n all_goals decide\n'
  txt+=f'#print axioms {k}_{phase}\nend AspisR1.NLR_Prepare\nend\n'
  (P/f'NLR_Prepare{kind}_{phase}.lean').write_text(txt)
 # Per-phase continuation equality. No code producing a native certificate here.
 txt='import NLR_PrepareDenote\n'+header
 par=par.replace('(s : State H)','(i : Input H)')
 txt+=f'theorem run_{phase} {par} :\n run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg ⟨i,.{phase} {a}⟩) (continuation cfg)) =\n run (NLR_PrepareTails.tail_{phase} cfg i {a}) := by\n'
 txt+=f' simp only [step,continuation,denote,advance,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,\n  NLR_PrepareTails.tail_{phase}]\n'
 txt+=' try rfl\n'+f'#print axioms run_{phase}\nend AspisR1.NLR_Prepare\nend\n'
 (P/f'NLR_PrepareRun_{phase}.lean').write_text(txt)
