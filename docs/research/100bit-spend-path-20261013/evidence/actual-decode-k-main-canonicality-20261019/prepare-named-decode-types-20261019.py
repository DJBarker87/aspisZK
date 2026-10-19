from pathlib import Path
import hashlib,json
repo=Path('/Users/dominic/ZK')
root=repo/'docs/research/100bit-spend-path-20261013/lean/extracted-decode-k-canonicality-20261018'
out=Path('/tmp/root-decode-main-named-instance-20261019');out.mkdir(exist_ok=True)
source=root/'AspisR1DecodeKFullV10/Types.lean';old=source.read_text()
assert old.count('@[discriminant isize]')==1
new=old.replace('@[discriminant isize]\n','')
marker='/-- [aspis_r1_cost_probe::r1_wire::ValidatedRecord]'
assert new.count(marker)==1
named='''-- Naming-only expansion of the emitted discriminant declaration. This
-- keeps the same constructor order and reader while allowing joint imports
-- with other generated Error owners.
def r1_wire.Error.read_discriminant (x : r1_wire.Error) : Isize :=
  match x with
  | .Allocation => 0#isize
  | .RowOrder _ _ => 1#isize
  | .InvalidRow => 2#isize
  | .Tag _ => 3#isize
  | .Length _ => 4#isize
  | .NonCanonical _ _ => 5#isize
  | .Boundary _ => 6#isize
  | .Terminal => 7#isize
  | .EqualCirclePoints => 8#isize
  | .TrailingBytes => 9#isize
  | .Public => 10#isize

instance _root_.AspisR1DecodeKFullV10.r1_wire.Error.instDiscriminant :
    Aeneas.Std.Discriminant r1_wire.Error Isize where
  read_discriminant := r1_wire.Error.read_discriminant

'''
new=new.replace(marker,named+marker)
f=out/'Types-named.lean';f.write_text(new)
runner=Path('/tmp/run-root-actual-decode-main-20261019.py').read_text()
runner=runner.replace("objects = Path('/tmp/root-merkle-cost-20261018/objects')", "objects = Path('/tmp/root-decode-main-named-instance-20261019/objects') if module.startswith('AspisR1DecodeK') or module == 'DecodeKOptionDiscriminantBridge' else Path('/tmp/root-merkle-cost-20261018/objects')")
runner=runner.replace("objects = Path('/tmp/root-decode-main-named-instance-20261019/objects')", "objects = Path('/tmp/root-decode-main-named-instance-20261019/objects')")
runner=runner.replace("leanpath = '","leanpath = '/tmp/root-decode-main-named-instance-20261019/objects:",1)
Path('/tmp/run-root-named-decode-main-20261019.py').write_text(runner)
(out/'naming-adapter.json').write_text(json.dumps({'original_source':str(source),'original_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'adapted_source':str(f),'adapted_source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'change':'Only generated discriminant reader/instance names; constructor order and reader mapping unchanged; no Rust source change.'},indent=2)+'\n')
print(f)
