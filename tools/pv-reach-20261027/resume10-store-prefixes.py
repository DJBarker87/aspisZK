"""Generate symbolic source prefix candidates at each native reservation effect.
No IO implementation or success assumption for the whole client is introduced.
"""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base='aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore'
# Each item is an actual prefix callback in reserve_fallible's success branch.
steps=[
 ('path','std.path.PathBuf',f'{base}.reservation_path {{store with last_error := none}} nonce'),
 ('options','std.fs.OpenOptions','std.fs.OpenOptions.new'),
 ('written','std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)','std.fs.OpenOptions.write options true'),
 ('created','std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)','std.fs.OpenOptions.create_new written.1 true'),
 ('moded','std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)','std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (written.2 (created.2 created.1)) 384#u32'),
 ('file','std.fs.File','std.fs.OpenOptions.open std.path.PathBuf.Insts.CoreConvertAsRefPath (moded.2 moded.1) path'),
 ('file1','std.fs.File','std.fs.File.Insts.StdIoWrite.write_all file (Array.to_slice aspis_prover.state_only_entropy.RESERVATION_MAGIC)'),
 ('file2','std.fs.File','std.fs.File.Insts.StdIoWrite.write_all file1 (Array.to_slice statement)'),
 ('file3','std.fs.File','std.fs.File.Insts.StdIoWrite.write_all file2 (Array.to_slice nonce)'),
 ('synced','Unit','std.fs.File.sync_all file3'),
 ('directory','std.path.Path','std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref store.directory'),
 ('dirsync','Unit','aspis_prover.state_only_entropy.sync_directory directory')]
# Native IO status lives inside Aeneas Result; each preceding success says exactly which
# native reply was returned, as opposed to treating inner Err as outer failure.
def reply(i,v):
 if i==5:return f'.Ok {v}'
 if i in [6,7,8]:return f'(.Ok (),{v})'
 if i in [9,11]:return '.Ok ()'
 return v
header='''import R1Z.PV_RE_BindTransport10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_StorePrefix10{idx:02d}
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
'''
for i,(name,ty,call) in enumerate(steps):
 args=' (store : Store) (statement nonce : Array U8 32#usize)'
 proof='  unfold '+base+'.reserve_fallible\n'
 for j,(v,t,c) in enumerate(steps[:i]):
  if j in [9,11]:args+=f'\n    (h{j} : {c} = .ok ({reply(j,v)}))'
  else:args+=f'\n    ({v} : {t}) (h{j} : {c} = .ok ({reply(j,v)}))'
  # Lift literal slices are definitional, except generic Aeneas lift.
  proof+=f'  change ∃ next, ({c} >>= _) = _\n  rw [h{j}]\n'
 proof+='  exact ⟨_,rfl⟩\n'
 text=header.format(idx=i)+f'''/-- Actual ordered reservation prefix {i}: all earlier native successes are explicit. -/
theorem prefix{args} :
    ∃ next, {base}.reserve_fallible store statement nonce =
      ({call} >>= next) := by
'''+proof+f'''#print axioms prefix
end R1Z.PV_RE_StorePrefix10{i:02d}
'''
 (L/f'PV_RE_StorePrefix10{i:02d}.lean').write_text(text)
# Keep exact generation arguments for subsequent client lifts/failure and divergence transport.
import json
(R/'evidence/pv-reach-20261027/resume10/store-prefix-plan.json').write_text(json.dumps(dict(steps=steps,native_success_indices=[5,6,7,8,9,11]),indent=2)+'\n')
