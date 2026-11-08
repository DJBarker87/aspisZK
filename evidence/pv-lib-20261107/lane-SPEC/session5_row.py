"""Write, compile and receipt ONE whole row, then commit before the next row.
No full replay, no row proof. Header extraction retains the package's literal
compiled prefix proposition instead of calling that prefix a whole contract.
"""
import hashlib,json,pathlib,re,subprocess,sys
L=pathlib.Path('evidence/pv-lib-20261107/lane-SPEC'); HOST='dombarker@100.108.41.90'; REM='/home/dombarker/project-offloads/codex-pv-lib-spec-20261107'
rows={15:(2,'PV_THR2_Source15Prologue','run'),208:(2,'PV_THR2_Catch208Invoke','issue'),220:(2,'PV_THR2_Intrinsic220ToInvoke','run'),316:(1,'PV_THR2_Catch316Prologue','run'),219:(1,'PV_THR2_Catch219Prologue','run'),125:(1,'PV_THR2_Catch125Prefix','run'),1:(3,'PV_FN_THREAD_f1Entry','prepare'),0:(2,'PV_FN_THREAD_f0Entry','request')}
def cmd(args,**kwargs): return subprocess.run(args,check=True,**kwargs)
def output(args):return subprocess.check_output(args,text=True)
def extract(s,name):
 start=re.search(r'^theorem '+re.escape(name)+r'\b',s,re.M).end(); head=s[start:s.index(':= by',start)].strip(); depth=0
 for j,c in enumerate(head):
  if c in '([{':depth+=1
  if c in ')]}':depth-=1
  if c==':' and depth==0:
   return head[:j].strip(),head[j+1:].strip()
 raise ValueError('missing conclusion')
def collect(attempt):
 cmd(['scp',f'{HOST}:{REM}/evidence/*-{attempt}.*',str(L)])
 receipt=json.loads((L/f'receipt-{attempt}.json').read_text());print(json.dumps({k:receipt[k] for k in ['attempt','target','exit','wall','peak_rss_kbytes','swaps'] if k in receipt}),flush=True)
 return receipt
if sys.argv[1]=='collect':
 a=int(sys.argv[2]);rec=collect(a)
 if rec['exit']:sys.exit(1)
 sys.exit(0)
n=int(sys.argv[1]);a=int(sys.argv[2]);arity,mod,theorem=rows[n];rev='41e76d01fdead952101594b8b0f36a7561d180f2' if n not in [0,1] else '18ca5e54ca03ee8b65a9838b1562b2fc1df6798c'
s=output(['git','show',rev+':lean/'+mod+'.lean']);binders,conclusion=extract(s,theorem)
spec=output(['git','show','5e397cb3878:evidence/pv-lib-20261107/PSPEC_thread_f'+str(n)+'.md'])
post=spec.split('## Post, frame and complete arms')[1].split('Every returned')[0].strip().replace('`','')
module=f'PV_LIB_SPEC_F{n}Whole';ns=module
extra=''
if n==1:
 extra=' ∧ ∃ n f flag, i.arguments = [.number n,f,flag] ∧ n < 2^64 ∧ ∃ b, r.carrier.truth flag = some b'
if n==0:
 extra=''' ∧ ∃ (F Task : Type) (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task) (closure : Data),
    i.arguments = [.number captures.n.val,closure] ∧
    PV_THR2_OrderedFamiliesEntryRefined.OrderedFamiliesEntryOwned' i.world captures closure'''
text=f'''import PV_LIB_SPEC_F166Whole
import {mod}
set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Row.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F{n}.live {arity} r i{extra}
/-- {post}
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_ThreadRow.Post table r PV_THR2_F{n}.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open {mod}
/-- Exact proposition of the package's {mod}.{theorem},
source {rev}. This is a PREFIX, not a previous whole contract.
Source SHA256 {hashlib.sha256(s.encode()).hexdigest()}. -/
def PackageStatement : Prop := ∀ {binders},
  {conclusion}
/-- Explicit side-by-side obligations. No implication, equivalence or proof
of the new whole contract is inferred from the package's prefix theorem. -/
def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PackageStatement ∧ Contract table r implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackageStatement
#print axioms Comparison
end {ns}
'''
p=pathlib.Path('lean')/(module+'.lean');assert not p.exists();p.write_text(text)
(L/f'SESSION5_PACKAGE_f{n}.json').write_text(json.dumps({'revision':rev,'path':'lean/'+mod+'.lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'theorem':mod+'.'+theorem,'literal_binders':binders,'literal_conclusion':conclusion,'new':module,'difference':spec.split('## Comparison to current package statements')[1].split('## Rejection example')[0].strip(),'new_machine':'PV_LIB_SPEC_D984.step; full table completed by lane A; no default'},indent=2)+'\n')
cmd(['scp',str(p),f'{HOST}:{REM}/sources/'])
cmd(['ssh',HOST,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'])
revnow=output(['git','rev-parse','HEAD']).strip()
r=subprocess.run(['ssh',HOST,f'python3 {REM}/host_attempt_s2.py {a} {module} {revnow} w3'],stdout=subprocess.DEVNULL)
rec=collect(a)
if r.returncode or not rec.get('accepted'):sys.exit(1)
with (L/'SESSION5.md').open('a') as f:f.write(f'\n## thread:f{n}\n\n{module}: whole Pre/MachineSpec/Post/Contract compiled{a};\nexact literal package prefix proposition plus comparison compiled in same module.\nNo row proof or comparison implication claimed. Wall{rec["wall"]};\npeak{rec["peak_rss_kbytes"]}KiB;swap{rec["swaps"]};standard summary axioms only.\n')
assert not any('sorryAx' in l for l in rec['axioms_summary_based'])
cmd(['git','add','--sparse',str(p),str(L)])
cmd(['git','commit','-m',f'State whole f{n} contract and literal package comparison'],stdout=subprocess.DEVNULL)
