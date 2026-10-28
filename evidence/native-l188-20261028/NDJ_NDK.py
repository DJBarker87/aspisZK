"""Revalidate the newly merged authoritative NDK refresh, unchanged code.

Only temporary script/association files are materialized; evidence remains
in immutable Git. No other branch/worktree is changed.
"""
from pathlib import Path
import tempfile,subprocess,importlib.util,sys,json,lzma,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
PACKAGE='25b55e53c4';PACKAGE=subprocess.check_output(['git','rev-parse',PACKAGE],cwd=R,text=True).strip()
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
prefix='evidence/native-ledger2-20261028/'
with tempfile.TemporaryDirectory(prefix='NDJ-ndk-') as td:
 d=Path(td)/'evidence'/'native-ledger2-20261028';d.mkdir(parents=True)
 for name in ['NDK_validate.py','NDK_review.py','NDK_ASSOCIATIONS.json']:(d/name).write_bytes(git('show',PACKAGE+':'+prefix+name))
 old=d.parent/'native-compledger-20261028';old.mkdir();(old/'NCZ_LEDGER.json').write_bytes((R/'evidence/native-compledger-20261028/NCZ_LEDGER.json').read_bytes())
 sys.path.insert(0,str(d));spec=importlib.util.spec_from_file_location('ndk',d/'NDK_validate.py');n=importlib.util.module_from_spec(spec);spec.loader.exec_module(n);n.ROOT=R
 snapshot=n.BASE
 def pinned_git(*args):return git(*(snapshot if a=='HEAD' else a for a in args))
 n.git=pinned_git
 def archived_read(self,p,cite=True):
  assert p in self.tree and self.head_tree.get(p)==self.tree[p][0],p
  if p not in self.cache:self.cache[p]=self.blob(self.tree[p][0])
  b=self.cache[p]
  if cite:self.used[p]={'sha256':n.sha(b),'bytes':len(b),'git_blob':self.tree[p][0],'revision':n.BASE}
  return b
 n.Store.read=archived_read
 actual=n.collect();n.validate_invariants(actual)
 expected=json.loads(git('show',PACKAGE+':'+prefix+'NDK_LEDGER.json'));assert actual==expected,'NDK full reconstruction differs'
 assert n.markdown(actual).encode()==git('show',PACKAGE+':'+prefix+'NDK_LEDGER.md'),'NDK summary differs'
 # Explicitly also retain the unchanged original NCZ structural validation.
 spec=importlib.util.spec_from_file_location('ncz',R/'evidence/native-compledger-20261028/NCZ_validate.py');original=importlib.util.module_from_spec(spec);spec.loader.exec_module(original);original.validate_invariants(actual)
 raw=n.dump(actual).encode();result=dict(exit_status=0,package_revision=PACKAGE,evidence_snapshot=snapshot,coverage=actual['coverage'],artifact_pins=len(actual['evidence_manifest']),frontier=len(actual['critical_path']['frontier']),snapshot_sha256=hashlib.sha256(raw).hexdigest(),validator='Unchanged NDK full reconstruction and summary + unchanged NCZ structural invariants; immutable Git Store adapter',trust_removed=0,composed_closed=0)
 if '--check' in sys.argv:
  assert json.loads((E/'NDJ_NDK_RESULT.json').read_text())==result
  assert lzma.decompress((E/'NDJ_NDK_SNAPSHOT.json.xz').read_bytes())==raw
 else:
  (E/'NDJ_NDK_SNAPSHOT.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NDJ_NDK_SNAPSHOT.json.sha256').write_text(result['snapshot_sha256']+'\n');(E/'NDJ_NDK_RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2))
