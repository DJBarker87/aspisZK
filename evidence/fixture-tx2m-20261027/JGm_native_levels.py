from pathlib import Path
import re,json,sys
R=Path(__file__).resolve().parents[2]

def term(s):
 s=s.lstrip()
 if s[0]=='(':
  n=0
  for i,c in enumerate(s):
   n+=(c=='(')-(c==')')
   if n==0:return s[:i+1],s[i+1:]
 return s.split(' ',1)
def ls(xs):return '['+','.join(xs)+']'
def val(n):return f'encodeState value{n}'
mods=[]
shapes=[]
for t,pre in [(0,'JGf'),(1,'JGh'),(2,'JGc')]:
 texts=[f.read_text() for f in sorted((R/'lean').glob(f'{pre}_TX2_M{t}Level*.lean'))]
 text='\n'.join(texts)+ (R/f'lean/{pre}_TX2_M{t}Leaves.lean').read_text()
 coords={ (int(h),int(b)//2**int(h)):n for h,b,n in re.findall(r'OracleDecisionMultiBuild.build indices f g (\d+) (\d+)=tree(\d+)',text)}
 addresses={n:tuple(x.strip() for x in term(args)) for n,args in re.findall(r'theorem address(\d+) : BinMerkle32Path.nodeInput \(children (.*)\)=input\d+ := by rfl',text)}
 # physical supplied sibling cell identities already compiled in JGh_.
 siblings={}
 for f in (R/'lean').glob('JGh_TX2_FrontierHeight*.lean'):
  for cell,st in re.findall(r'theorem k'+str(t)+r'c(\d+)_read :[^\n]*=([^\n]+) :=',f.read_text()):
   siblings[int(cell)]=(f.stem,st.strip())
 # Actual frontier counts, sorted input keys, no mergeSort evaluated in Lean.
 indices=sorted(b for (h,b) in coords if h==0)
 count=163 if t<2 else 141
 cell=0
 for h in range(18):
  ns=f'JGm_TX2_Level{t}_{h:02}'
  mods.append(ns)
  inds=sorted(b for (k,b) in coords if k==h)
  outs=sorted(b for (k,b) in coords if k==h+1)
  current=[f'{x}#u32' for x in inds]
  values=[val(coords[h,x]) for x in inds]
  startcell=cell
  s=f'''import JGm_TX2_ParentCalls{t}
import JGm_TX2_View
import JGm_TX2_RowControl
import JGm_TX2_ExternalRun
import JGm_TX2_Supplied
import JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open {pre}_TX2_M{t}Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes{t}
'''
  # Invariant arrays are only the live prefix (at most12 elements).
  s+=f'def indices00 : List U32 := {ls(current)}\ndef values00 : List (Array U8 32#usize) := {ls(values)}\ndef s00 (s : reference.Scratch) := s\n'
  rows=[];i=0
  for w,p in enumerate(outs):
   k=inds[i];n=coords[h+1,p];left,right=addresses[n]
   pair=i+1<len(inds) and inds[i+1]==(k^1)
   ni=i+2 if pair else i+1
   before=cell
   if not pair:cell+=1
   nw=w+1
   cur=f's{w:02}';nxt=f's{nw:02}'
   current[w]=f'{p}#u32'; values[w]=val(n)
   s+=f'''def {nxt} (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after ({cur} s) {k}#u32 {w}#usize ({val(n)}) {32*cell}#usize
 def indices{nw:02} : List U32 := {ls(current)}
 def values{nw:02} : List (Array U8 32#usize) := {ls(values)}
'''
   rows.append(dict(w=w,k=k,n=n,left=left,right=right,i=i,ni=ni,pair=pair,before=before,cell=cell))
   i=ni
  last=len(rows)
  shapes.append(dict(module=ns,tree=t,height=h,input_indices=inds,parent_indices=outs,cursor_start=32*startcell,cursor_end=32*cell,rows=rows))
  s+=f'''def output (s : reference.Scratch) : reference.Scratch := {{s{last:02} s with n:={last}#usize}}
 def indicesOut : List U32 := {ls([f'{x}#u32' for x in outs])}
 def valuesOut : List (Array U8 32#usize) := {ls([val(coords[h+1,x]) for x in outs])}
 theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 {32*startcell}) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes{t} 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut {32*cell} := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 {32*startcell} := view
'''
  for r in rows:
   w,k,n,left,right,i,ni,pair,before,c=(r[z] for z in ['w','k','n','left','right','i','ni','pair','before','cell'])
   now=f's{w:02}'; nxt=f's{w+1:02}'; xs=f'indices{w:02}';ys=f'values{w:02}';v=f'v{w:02}'
   s+=f'''  have ri{w:02} : Array.index_usize ({now} s).idx {i}#usize=ok {k}#u32 :=
    JGm_TX2_View.index ({now} s) {xs} {ys} {32*before} {v} {i}#usize (by decide)
  have rv{w:02} : Array.index_usize ({now} s).val {i}#usize=ok ({val(coords[h,k])}) :=
    JGm_TX2_View.value ({now} s) {xs} {ys} {32*before} {v} {i}#usize (by decide)
  have active{w:02} : {i}#usize<({now} s).n := by
    change ({i}:Nat)<({now} s).n.val
    rw [{v}.size]
    decide
  have cursor{w:02} : ({now} s).«at»={32*before}#usize := UScalar.eq_of_val_eq {v}.at_eq
'''
   if pair:
    s+=f'''  have rn{w:02} : Array.index_usize ({now} s).idx {i+1}#usize=ok ({k}#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index ({now} s) {xs} {ys} {32*before} {v} {i+1}#usize (by decide)
  have rr{w:02} : Array.index_usize ({now} s).val {i+1}#usize=ok ({val(coords[h,inds[i+1]])}) :=
    JGm_TX2_View.value ({now} s) {xs} {ys} {32*before} {v} {i+1}#usize (by decide)
  have selected{w:02} := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash ({now} s)
    JGm_TX2_Supplied.nodes{t} {i}#usize {w}#usize {i+1}#usize {ni}#usize {k}#u32
    (encodeState {left}) (encodeState {right}) ri{w:02} rv{w:02}
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change ({i+1}:Nat)<({now} s).n.val;rw [{v}.size];decide)
    rn{w:02} rr{w:02} (JGm_TX2_Scalar.add _ _ _ rfl)
'''
   else:
    st=siblings[before][1]
    # Ensure inherited cell has precisely the model's supplied child.
    expected=left if k%2 else right
    if expected.startswith('('):expected=expected[1:-1]
    assert st.startswith(f"{pre}_TX2_M{t}Roots.siblingAt "),(t,h,before,st)
    s+=f'''  have unpaired{w:02} : ∀ more : {ni}#usize<({now} s).n,
      ∃ other,Array.index_usize ({now} s).idx {ni}#usize=ok other ∧ other≠{k}#u32 ^^^ 1#u32 := by
'''
    if ni<len(inds):
     s+=f'''    intro _
    exact ⟨{inds[ni]}#u32,JGm_TX2_View.index ({now} s) {xs} {ys} {32*before} {v} {ni}#usize (by decide),by decide⟩
'''
    else:
     s+=f'''    intro more
    change ({ni}:Nat)<({now} s).n.val at more
    rw [{v}.size] at more
    exact False.elim ((by decide : ¬({ni}:Nat)<{len(inds)}) more)
'''
    s+=f'''  have read{w:02} : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes{t}
      ({now} s).«at» {32*c}#usize)=ok (encodeState ({expected})) := by
    rw [cursor{w:02}]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes{t} {before}
      {count*32}#usize {32*before}#usize {32*c}#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length{t}];decide)
    rw [JGh_TX2_Siblings{h:02}.k{t}c{before:03}_read] at read
    simpa only [JGm_TX2_Supplied.nodes{t},{pre}_TX2_M{t}Roots.siblingAt] using read
  have selected{w:02} := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash ({now} s)
    JGm_TX2_Supplied.nodes{t} {i}#usize {w}#usize {ni}#usize {32*c}#usize {32*(count-before)}#usize
    {k}#u32 ({val(coords[h,k])}) (encodeState ({expected})) ri{w:02} rv{w:02}
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired{w:02}
    (by have len : Slice.len JGm_TX2_Supplied.nodes{t}={count*32}#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length{t}
        rw [len,cursor{w:02}];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor{w:02}];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor{w:02}];decide)
    (by rw [JGm_TX2_Supplied.length{t}];decide) read{w:02}
  simp only [show {k}#u32 &&& 1#u32={k%2}#u32 from rfl,''' + ('if_pos rfl' if k%2==0 else 'if_neg (by decide : 1#u32≠0#u32)')+f'''] at selected{w:02}
'''
   s+=f'''  have row{w:02} : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      ({now} s) JGm_TX2_Supplied.nodes{t} {i}#usize {w}#usize=
        ok (.Next ({nxt} s) {ni}#usize {w+1}#usize) := by
    rw [selected{w:02}]
'''
   if pair:s+=f'    rw [cursor{w:02}]\n'
   s+=f'''    exact JGm_TX2_ParentCalls{t}.source{n} D hash ({now} s) {ni}#usize {32*c}#usize {k}#u32 {w}#usize (by decide)
  have v{w+1:02} : JGm_TX2_View.View ({nxt} s) indices{w+1:02} values{w+1:02} {32*c} := by
    have v := JGm_TX2_View.after ({now} s) {xs} {ys} {32*before} {v}
      {k}#u32 {w}#usize ({val(n)}) {32*c}#usize (by decide)
    exact v
'''
  s+='  constructor\n  · calc\n'
  for j,r in enumerate(rows):
   w,i,ni=(r[z] for z in ['w','i','ni']);now=f's{w:02}';nxt=f's{w+1:02}'
   lhs=f'reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash ({now} s) JGm_TX2_Supplied.nodes{t} {i}#usize {w}#usize' if j==0 else '_'
   s+=f'''      {lhs} = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash ({nxt} s) JGm_TX2_Supplied.nodes{t} {ni}#usize {w+1}#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active{w:02} row{w:02}
'''
  s+=f'''      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s{last:02} s).n.val≤{len(inds)};rw [v{last:02}.size];decide)
  · exact JGm_TX2_View.finish (s{last:02} s) indices{last:02} values{last:02} {32*cell}
      v{last:02} {last}#usize (by decide)
#print axioms source
end AspisR1.{ns}
end
'''
  out=R/f'lean/{ns}.lean'
  if '--check' in sys.argv:
   assert out.read_text()==s,ns
  else:out.write_text(s)
 assert cell==count,(t,cell,count)
P=Path(__file__).resolve().parent
(P/'JGm_LEVEL_SHAPES.json').write_text(json.dumps(shapes,indent=2)+'\n')
(P/'JGm_LEVEL_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n')
print('Generated' if '--check' not in sys.argv else 'Checked',len(mods),'native level modules')
