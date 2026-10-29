from pathlib import Path
p=Path(__file__).with_name('PV_DIAG6_Native.lean');s=p.read_text();s=s.removesuffix('end PV_DIAG6\n')
def add(name,binders,lhs,rhs,proof):
 global s
 s+='-- STAGE\ntheorem '+name+'\n '+binders+' :\n '+lhs+' = '+rhs+' := by\n '+proof+'\n#print axioms '+name+'\n'
for kind,ty,ctor in [('panic','Panic','.panic p'),('abort','Crash','.abort p'),('diverge',None,'.diverge')]:
 extra=' (p : '+ty+')' if ty else ''
 b='(o : WriteOps S E) (bs : Bytes) (s t : S) (es : List Event)'+extra+'\n (k : Bytes → Op S (Except E Unit)) (hne : bs.isEmpty = false)\n (h : o.write bs s = ⟨es,t,'+ctor+'⟩)'
 add('write_leaf_'+kind,b,'writeAllStep o bs k s','⟨es,t,'+ctor+'⟩','simp [writeAllStep,hne,sequence,h,PV_DIAG3.bind]')
 b='(o : WriteOps S E) (bs : Bytes) (s t u : S) (es gs : List Event) (e : E)'+extra+'\n (k : Bytes → Op S (Except E Unit)) (hne : bs.isEmpty = false)\n (hw : o.write bs s = ⟨es,t,.value (.error e)⟩)\n (hg : o.interruptedGuard e t = ⟨gs,u,'+ctor+'⟩)'
 add('write_guard_'+kind,b,'writeAllStep o bs k s','⟨es++gs,u,'+ctor+'⟩','simp [writeAllStep,hne,sequence,hw,hg,PV_DIAG3.bind,prepend]')
 b='(o : WriteOps S E) (bs : Bytes) (s t u v : S) (es gs ds : List Event) (e : E)'+extra+'\n (k : Bytes → Op S (Except E Unit)) (hne : bs.isEmpty = false)\n (hw : o.write bs s = ⟨es,t,.value (.error e)⟩)\n (hg : o.interruptedGuard e t = ⟨gs,u,.value true⟩)\n (hd : o.dropInterrupted e u = ⟨ds,v,'+ctor+'⟩)'
 add('write_drop_'+kind,b,'writeAllStep o bs k s','⟨es++(gs++ds),v,'+ctor+'⟩','simp [writeAllStep,hne,sequence,hw,hg,hd,PV_DIAG3.bind,prepend]')
 if kind!='abort':
  b='(o : FmtOps S E) (s t : S) (es : List Event)'+extra+'\n (h : o.format s = ⟨es,t,'+ctor+'⟩)'
  add('formatter_leaf_'+kind,b,'defaultFmt o s','⟨es,t,'+ctor+'⟩','simp [defaultFmt,sequence,h,PV_DIAG3.bind]')
 b='(w : Bytes → Op S (Except E Unit)) (d : E → Op S Unit)\n (bs : Bytes) (s t : S) (es : List Event)'+extra+'\n (h : w bs s = ⟨es,t,'+ctor+'⟩)'
 add('adapter_write_'+kind,b,'adapterWrite w d bs s','⟨es,t,'+ctor+'⟩','simp [adapterWrite,sequence,h,PV_DIAG3.bind]')
 b='(w : Bytes → Op S (Except E Unit)) (d : E → Op S Unit)\n (bs : Bytes) (s t u : S) (es ds : List Event) (e : E)'+extra+'\n (hw : w bs s = ⟨es,t,.value (.error e)⟩)\n (hd : d e t = ⟨ds,u,'+ctor+'⟩)'
 add('adapter_store_'+kind,b,'adapterWrite w d bs s','⟨es++ds,u,'+ctor+'⟩','simp [adapterWrite,sequence,hw,hd,PV_DIAG3.bind,prepend]')
 b='(cap : Op S Bool) (w : Op S Unit) (s t : S) (es : List Event)'+extra+'\n (h : cap s = ⟨es,t,'+ctor+'⟩)'
 add('stderr_capture_'+kind,b,'attemptStderr cap w s','⟨es,t,'+ctor+'⟩','simp [attemptStderr,sequence,h,PV_DIAG3.bind]')
 b='(w : Op S (Except E Unit)) (d : Except E Unit → Op S Unit)\n (s t : S) (es : List Event)'+extra+'\n (h : w s = ⟨es,t,'+ctor+'⟩)'
 add('ignored_write_'+kind,b,'ignoredWrite w d s','⟨es,t,'+ctor+'⟩','simp [ignoredWrite,sequence,h,PV_DIAG3.bind]')
p.write_text(s+'end PV_DIAG6\n')
