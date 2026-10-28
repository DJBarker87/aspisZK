"""Read-only source/cut ledger. Token equality is source association, not a
Rust semantics theorem. All deliberate cut/parameter rewrites stay explicit."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
R=E.parents[1]
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(name):return subprocess.check_output(['git','show',F+':'+name],cwd=R).decode()
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def body(s,mark):
 p=s.index('{',s.index(mark));depth=1;i=p+1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 return s[p+1:i-1]
def tokens(s):
 s=re.sub(r'//[^\n]*','',s)
 return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',s)
candidate=frozen('crates/aspis-r1-cost-probe/src/candidate.rs')
verifier=frozen('crates/aspis-r1-cost-probe/src/verifier.rs')
sampler=frozen('crates/aspis-r1-cost-probe/src/sampler.rs')
cut=(E/'NBL_K012/sources/NBL_src/crates/aspis-r1-cost-probe/src/NBL_candidate.rs').read_text()
native=body(candidate,'fn prepare<')
suffix=native[native.index('let sem ='):]
local=body(cut,'fn NBL_after_view<')
# Source v is owned and borrowed for new; cut's v parameter IS that borrow.
expected=suffix.replace('Prepared::new(&sem, &v,','Prepared::new(&sem, v,')
checks=[dict(name='K012 after-wide-view suffix',same=tokens(expected)==tokens(local),
 source='candidate::prepare from let sem through Prepared::new',
 rewrites=['cut receives &View; remove redundant & at Prepared::new'],
 native_sha256=sha(suffix),cut_sha256=sha(local),credit='error routing only; semantic producer not proved')]
nba_patch=(R/'evidence/native-prepare1-20261027/NBA_K021-harness.patch').read_text()
nba='\n'.join(l[1:] for l in nba_patch.splitlines() if l.startswith('+') and not l.startswith('+++'))
new=body(verifier,'pub fn new<H:Digest32>')
tail=new[new.index('*g=powers'):]
# Isolated source suffix uses explicit prior locals and named Prepared.
expected=tail.replace('Box::new(Self{','Box::new(Prepared{')
local=body(nba,'fn NBA_tail<')
checks.append(dict(name='NBA tail cut',same=tokens(expected)==tokens(local),
 source='Prepared::new from scratch overwrite to return',rewrites=['Self -> Prepared'],
 native_sha256=sha(tail),cut_sha256=sha(local),
 credit='read-only inherited cut, local source association; not trace construction'))
init_source=body(sampler[sampler.index('fn qm31_digits'):],'while i < 8')
init=(E/'NBL_K011/sources/NBL_src/crates/aspis-r1-cost-probe/src/NBL_candidate.rs').read_text()
local=body(init,'fn NBL_init_step')
expected=init_source.replace('4 * i','4 * (*i)').replace('rank[i]','rank[*i]').replace('i +=','*i +=')
# Rust allows a trailing comma in the array initializer.
tok=lambda s:[t for j,t in enumerate(tokens(s)) if not(t==',' and j+1<len(tokens(s)) and tokens(s)[j+1]==']')]
checks.append(dict(name='K011 qm31 initialization ONE iteration',same=tok(expected)==tok(local),
 rewrites=['loop index local -> mutable index reference','ignore trailing array comma'],
 native_sha256=sha(init_source),cut_sha256=sha(local),
 credit='one iteration frame; NBL_InitTrace.rho gives ordered input after induction'))
# Frozen corpus integrity includes every tracked crates/programs file and lock.
names=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'--','crates','programs','Cargo.lock'],cwd=R,text=True).splitlines()
changed=[]
for n in names:
 p=R/n
 h=hashlib.sha256(subprocess.check_output(['git','show',F+':'+n],cwd=R)).hexdigest()
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=h:changed.append(n)
report=dict(revision=F,current_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 checks=checks,all_cut_token_checks=all(c['same'] for c in checks),
 frozen_files=len(names),frozen_source_differences=changed,
 limitations=['No Rust interpreter/source refinement follows from token equality alone.',
 'Closed native callee bridges are cited with domains; missing caller native producers remain explicit dependencies.',
 'No XRn_Join correspondence kit is used.'])
(E/'NBL_ASSOCIATIONS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['checks']}))
for c in checks:print(c['name'],c['same'])
if changed or not report['all_cut_token_checks']:raise SystemExit(1)
