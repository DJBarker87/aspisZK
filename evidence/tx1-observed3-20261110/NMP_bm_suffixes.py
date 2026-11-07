from pathlib import Path
E=Path(__file__).resolve().parent
head='''import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMP_ObservedSteps (State execute body)
open NMT_CallTree (erase)
'''
text=head+'''def f5 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix)
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
'''
(E/'NMP_ObservedNormal.lean').write_text(text)
args=['','(p : r1_wire.Prefix)','(p : r1_wire.Prefix)','(p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)','(p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges)','(p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges)']
states=['.parse s','.mark0 s p','.publicTranscript s p','.begin_ s p t','.mark1 s p t ch','.finish s p t ch']
extra=['',' p',' p',' p t',' p t ch',' p t ch']
for i in range(5,-1,-1):
 dep='NMP_ObservedNormal' if i==5 else 'NMP_ObservedSuffix'+str(i+1)
 laws='[NMP_ObservedSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div'+('' if i==5 else ',fold'+str(i+1))+',f'+str(i)+']'
 # One primitive call and one already-proved suffix per target; no whole-machine unfolding.
 proof=''' rw [execute]
 simp only '''+laws+'''
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only '''+laws+''')
 | (split <;> simp only '''+laws+''')
'''
 if i<=3:proof=proof.replace('intro x; simp only','intro x; try simp only').replace('split <;> simp only','split <;> try simp only')
 if i==3:
  proof=' rw [execute]\n simp only '+laws+'\n apply NMT_CallTree.result_congr\n rintro ⟨r,after⟩\n cases r <;> simp only '+laws+' <;> rfl\n'
 text=head.replace('import NMP_ObservedState','import '+dep+'\nimport NMP_DirectBind')+f'''/-- One source occurrence and the already-compiled suffix; all Result arms. -/
theorem fold{i} {{H W : Type}} (c : Calls) (s : Parent H W) {args[i]} :
 erase (execute c {6-i} ({states[i]})) = f{i} c s{extra[i]} := by
'''+proof+f'#print axioms fold{i}\nend AspisR1.NMP_ObservedSuffix\n'
 (E/('NMP_ObservedSuffix'+str(i)+'.lean')).write_text(text)
print('Drafted one normalized definition module and six isolated erasure suffixes')
