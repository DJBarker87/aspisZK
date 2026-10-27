"""Separate native inner IO errors from backend failure/divergence."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RE_StorePrefix1005.lean').read_text();args=s.split('theorem prefix',1)[1].split(' :\n    ∃ next',1)[0];proof=s.split(' := by\n',1)[1].split('#print axioms',1)[0].replace('change ∃ next,','change').replace('  exact ⟨_,rfl⟩','')
base='aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore'
head=s.split('theorem prefix',1)[0].replace('PV_RE_StorePrefix1005','PV_RE_StoreOpenErrors10')
text=head
for name,b,res in [('already_exists','true','.Ok false'),('other_error','false','.Err error')]:
 extra='''
    (error : std.io.error.Error) (kind : core.io.error.ErrorKind)
    (opened : std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path = .ok (.Err error))
    (classified : std.io.error.Error.kind error = .ok kind)
    (compared : core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq kind core.io.error.ErrorKind.AlreadyExists = .ok '''+b+'))'
 text+='theorem '+name+args+extra+f''' :
    {base}.reserve_fallible store statement nonce = .ok ({res},{{store with last_error := none}}) := by
'''+proof+'''  change (std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path >>= _) = _
  rw [opened]
  change (std.io.error.Error.kind error >>= _) = _
  rw [classified]
  change (core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq kind core.io.error.ErrorKind.AlreadyExists >>= _) = _
  rw [compared]
  rfl
#print axioms '''+name+'\n'
text+='end R1Z.PV_RE_StoreOpenErrors10\n';(L/'PV_RE_StoreOpenErrors10.lean').write_text(text)
