from pathlib import Path
import json
D=Path(__file__).resolve().parent
plans=json.loads((D/'plans.json').read_text())
def extend(m,name,stmt,proof):
 s=plans[m][-1].removesuffix('end PV_DIAG11\n')+'theorem '+name+' '+stmt+' := '+proof+'\n#print axioms '+name+'\nend PV_DIAG11\n'
 plans[m].append(s);(D/(m+'.lean')).write_text(s)
extend('PV_DIAG11_Execution','map_error_normal_result','{V E F A : Type} (f : E → F) (es : List V) (e : E) : mapError f (⟨es,.error e⟩ : Run V E A)=⟨es,.error (f e)⟩','rfl')
extend('PV_DIAG11_WriteAll','writeAll_interrupted_drop_panics','{V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es ds : List V) (h : w (b::bs)=⟨es,.error .interrupted⟩) : writeAll w ⟨ds,.panic⟩ (fuel+1) (b::bs)=⟨es++ds,.panic⟩','by simp only [writeAll,h,seq,pre]')
extend('PV_DIAG11_Cleanup','drop_error_drop_oom','{V E A : Type} (es ds : List V) (e : E) : dropReturned (⟨es,.error e⟩ : Run V E A) ⟨ds,.oom⟩=⟨es++ds,.oom⟩','rfl')
extend('PV_DIAG11_File','file_write_error_close_oom','{V F : Type} (es ws ds : List V) (f : F) (e : IoError) : fileWrite (⟨es,.ok f⟩ : Run V IoError F) (fun _ => ⟨ws,.error e⟩) (fun _ => ⟨ds,.oom⟩)=⟨es++(ws++ds),.oom⟩','rfl')
extend('PV_DIAG11_Print','stderr_error_drop_panics','{V : Type} (es ws ds : List V) (e : IoError) : attemptStderr (⟨es,.ok false⟩ : Run V IoError Bool) ⟨ws,.error e⟩ (fun _ => ⟨ds,.panic⟩)=⟨es++(ws++ds),.panic⟩','rfl')
extend('PV_DIAG11_Report','report_error_drop_panics','{V E A : Type} (e : E) (es ds : List V) (ok : A → Run V IoError Nat) : report (.error e) ok (fun _ => ⟨es,.ok ()⟩) (fun _ => ⟨ds,.panic⟩)=⟨es++ds,.panic⟩','by simp only [report,seq,ret,pre,dropReturned,List.append_nil]')
extend('PV_DIAG11_Client','main_print_panics','{V J : Type} (es ps : List V) (j : J) : actionMain (⟨es,.ok j⟩ : Run V IoError J) (fun _ => ⟨ps,.panic⟩)=⟨es++ps,.panic⟩','rfl')
def mod(m,imports,defs,ths):
 s='\n'.join('import '+x for x in imports)+'\nset_option autoImplicit false\nnamespace PV_DIAG11\n'+defs+'\n'
 out=[]
 for n,stmt,p in ths:
  s+='theorem '+n+' '+stmt+' := '+p+'\n#print axioms '+n+'\n';out.append(s+'end PV_DIAG11\n')
 plans[m]=out;(D/(m+'.lean')).write_text(out[-1])
mod('PV_DIAG11_Public',['PV_DIAG10_Operands','PV_DIAG2_Effects'],r'''
/-! Scoped unit-error operand producer and log-0.4.34 initial selection.
The variant law is a consumed L1 input; it is NOT derived from environment.
No theorem here excludes reached logger setters or binds native frames. -/
def unitErrorCall (site : Nat) (e : PV_DIAG2.Error) (frames : PV_DIAG9.Stack) (level : Nat) : PV_DIAG9.DiagnosticCall :=
 ⟨site,[PV_DIAG2.spelling e],frames,level⟩
structure LoggerState where
 initialized : Nat
 binding : Nat
 maxLevel : Nat
 deriving DecidableEq
def initialLogger : LoggerState := ⟨0,0,0⟩
def selectedLogger (s : LoggerState) : Nat := if s.initialized=2 then s.binding else 0
''',[
('unit_error_operand_link','{I P : Type} (context : I → P) (site level : I → Nat) (errors : I → PV_DIAG2.Error) (frames : I → PV_DIAG9.Stack) (variants : ∀ i j, context i=context j → errors i=errors j) : PV_DIAG10.PV_DIAG10_Link_Operands context (fun i => unitErrorCall (site i) (errors i) (frames i) (level i))','by intro i j h; change [PV_DIAG2.spelling (errors i)]=[PV_DIAG2.spelling (errors j)]; rw [variants i j h]'),
('logger_initial_disabled','(level : Nat) (positive : 0<level) : selectedLogger initialLogger=0 ∧ ¬ (level ≤ initialLogger.maxLevel)','by\n constructor\n · rfl\n · exact Nat.not_le_of_lt positive'),
('logger_not_initialized','(s : LoggerState) (h : s.initialized≠2) : selectedLogger s=0','by exact if_neg h'),
])
mod('PV_DIAG11_Requests',['PV_DIAG11_WriteAll','PV_DIAG10_Requests'],r'''
/-! Metadata at the generic write_all loop. Buffer contents are separate.
Actual fd/path/offset/allocator/entropy/logger request provenance is OPEN.
WorldBlind and the original ChargedBad association belong to other lines.
The V400 source-local result below needs equal initial lengths and a
metadata/reply-only write primitive; neither is asserted for all native calls. -/
open PV_DIAG9
structure WriteCursor where
 offset : Nat
 remaining : Nat
 retries : Nat
 deriving DecidableEq
def advance (c : WriteCursor) (n : Nat) : WriteCursor :=
 ⟨c.offset+n,c.remaining-n,c.retries⟩
def interrupted (c : WriteCursor) : WriteCursor := ⟨c.offset,c.remaining,c.retries+1⟩
def writeRequest (target : List Nat) (align address limit : Nat) (c : WriteCursor) : FaultRequest :=
 ⟨1,target,c.offset,min c.remaining limit,align,address,c.retries⟩
''',[
('write_request_size','(target : List Nat) (align address limit : Nat) (c : WriteCursor) : (writeRequest target align address limit c).size=min c.remaining limit','rfl'),
('write_slice_length','(a b : List UInt8) (n : Nat) (h : a.length=b.length) : (a.drop n).length=(b.drop n).length','by simp only [List.length_drop,h]'),
('write_progress_offset','(c : WriteCursor) (n : Nat) : (advance c n).offset=c.offset+n ∧ (advance c n).remaining=c.remaining-n','⟨rfl,rfl⟩'),
('write_interrupted_preserves_buffer','(c : WriteCursor) : (interrupted c).offset=c.offset ∧ (interrupted c).remaining=c.remaining ∧ (interrupted c).retries=c.retries+1','⟨rfl,rfl,rfl⟩'),
('write_request_from_public_cursor','{I P : Type} (context : I → P) (c : I → WriteCursor) (publicCursor : ∀ i j, context i=context j → c i=c j) (target : List Nat) (align address limit : Nat) (i j : I) (h : context i=context j) : writeRequest target align address limit (c i)=writeRequest target align address limit (c j)','by rw [publicCursor i j h]'),
('writeAll_same_length_metadata','{V : Type} (w : List UInt8 → Run V IoError Nat) (d : Run V IoError Unit) (primitive : ∀ (a b : List UInt8), a.length=b.length → w a=w b) (fuel : Nat) (a b : List UInt8) (len : a.length=b.length) : writeAll w d fuel a=writeAll w d fuel b',r'''by
 induction fuel generalizing a b with
 | zero =>
   cases a with
   | nil => cases b with
     | nil => rfl
     | cons y ys => simp at len
   | cons x xs => cases b with
     | nil => simp at len
     | cons y ys => rfl
 | succ fuel ih =>
   cases a with
   | nil => cases b with
     | nil => rfl
     | cons y ys => simp at len
   | cons x xs => cases b with
     | nil => simp at len
     | cons y ys =>
       have same := primitive (x::xs) (y::ys) len
       cases hw : w (x::xs) with
       | mk es ex =>
         have hb : w (y::ys)=⟨es,ex⟩ := same.symm.trans hw
         cases ex with
         | ok n =>
           cases n with
           | zero => simp only [writeAll,hw,hb]
           | succ n =>
             have hd := write_slice_length (x::xs) (y::ys) (n+1) len
             simp only [writeAll,hw,hb]
             rw [len,ih _ _ hd]
         | error e =>
           cases e with
           | interrupted =>
             simp only [writeAll,hw,hb]
             rw [ih _ _ len]
           | writeZero => simp only [writeAll,hw,hb]
           | other code => simp only [writeAll,hw,hb]
         | panic => simp only [writeAll,hw,hb]
         | oom => simp only [writeAll,hw,hb]
         | abort => simp only [writeAll,hw,hb]
         | diverge => simp only [writeAll,hw,hb]'''),
('writeAll_metadata_public','{I P V : Type} (context : I → P) (buf : I → List UInt8) (lengths : ∀ i j, context i=context j → (buf i).length=(buf j).length) (w : List UInt8 → Run V IoError Nat) (d : Run V IoError Unit) (primitive : ∀ (a b : List UInt8), a.length=b.length → w a=w b) (fuel : Nat) (i j : I) (h : context i=context j) : writeAll w d fuel (buf i)=writeAll w d fuel (buf j)','writeAll_same_length_metadata w d primitive fuel _ _ (lengths i j h)'),
('writeAll_one_reply_not_termination','{V : Type} (es : List V) (b : UInt8) (bs : List UInt8) : writeAll (fun _ => (⟨es,.error .interrupted⟩ : Run V IoError Nat)) (ret ()) 1 (b::bs)=⟨es,.diverge⟩','by simp only [writeAll,seq,ret,pre,List.nil_append]'),
])
plans['PV_DIAG11_Requests']=plans['PV_DIAG11_Requests'][:7]
(D/'PV_DIAG11_Requests.lean').write_text(plans['PV_DIAG11_Requests'][-1])
(D/'plans.json').write_text(json.dumps(plans,indent=2)+'\n')
