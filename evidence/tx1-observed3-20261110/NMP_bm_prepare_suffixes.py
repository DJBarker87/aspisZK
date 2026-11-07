from pathlib import Path
E=Path(__file__).resolve().parent
head='''set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (erase)
'''
args=['','(logical : alloc.vec.Vec U8)','(semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)','(semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)','(semantic y1 : Slice U8)','(v : verifier.View)','(v : verifier.View) (sem : r1_semantic.Verified H)','(v : verifier.View) (sem : r1_semantic.Verified H)']
states=['.allocate s','.split s logical','.semantic s semantic y1 back vecBack','.values s semantic y1 back vecBack','.view s semantic y1','.observed s v','.mark s v sem','.prepared s v sem']
extra=['',' logical',' semantic y1 back vecBack',' semantic y1 back vecBack',' semantic y1',' v',' v sem',' v sem']
for i in range(7,-1,-1):
 dep='NMP_PrepareNormal' if i==7 else 'NMP_PrepareSuffix'+str(i+1)
 laws='[NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div'+('' if i==7 else ',fold'+str(i+1))+',f'+str(i)+']'
 text='import '+dep+'\n'+head+f'''/-- One source call and the already-compiled suffix; no whole-state unfolding. -/
theorem fold{i} {{H W : Type}} (c : Calls) (s : Parent H W) {args[i]} :
 erase (execute c {8-i} ({states[i]})) = f{i} c s{extra[i]} := by
 rw [execute]
 simp only '''+laws+'''
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only '''+laws+''')
 | (split <;> simp only '''+laws+''')
'''+f'#print axioms fold{i}\nend AspisR1.NMP_PrepareSuffix\n'
 (E/f'NMP_PrepareSuffix{i}.lean').write_text(text)
print('Drafted eight isolated prepare erasure suffixes')
