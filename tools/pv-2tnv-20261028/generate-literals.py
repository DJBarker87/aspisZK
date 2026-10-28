from pathlib import Path
import json,re,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume';b=(R/'lean/PV_2TNV_ByteEncoding.lean').read_text();rows={r['name']:r for r in json.load(open(E/'byte-generation.json'))['fields']}
vec=lambda xs:'!['+','.join(map(str,xs))+']'
s='''import PV_2TNV_PublicWindows
import R1Z.PV_RunJoin_RootModelTable
import R1Z.PV_RunJoin_OutputCell3917
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_PublicLiterals
open Aeneas Aeneas.Std R0P PV_2TNV_PublicEncoding PV_2TNV_PublicWindows
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

theorem digest_drop (bytes : List U8) (off start : Nat) :
    digest (bytes.drop off) start = digest bytes (off+start) := by
  funext i
  unfold digest word
  rw [List.drop_drop,Nat.add_assoc]

'''
for k in range(47):
 name=f'digest_{k:02}';raw=list(map(int,re.findall(r'(\d+)#u8',re.search(r'def '+name+r'_bytes[^\n]*',b)[0])));assert len(raw)==32
 xs=[int.from_bytes(bytes(raw[i:i+4]),'little') for i in range(0,32,4)];off=rows[name]['offset']
 s+=f'def d{k:02} : Digest M := {vec(xs)}\n'
 s+=f'theorem read{k:02} : digest JFx_DataPublic00.bytes {off} = d{k:02} := by\n  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.{name}_selected]\n  funext i\n  fin_cases i <;> rfl\n#print axioms read{k:02}\n'
s+='''theorem anchor : nativePublic.anchor = d43 := by
  change digest (JFx_DataPublic00.bytes.drop 1664) 80 = d43
  rw [digest_drop]
  exact read43
theorem nullifier : nativePublic.nullifier = d44 := by
  change digest (JFx_DataPublic00.bytes.drop 1664) 112 = d44
  rw [digest_drop]
  exact read44
theorem asset : nativePublic.assetId = 77 := by
  change (PV_2TNV_ByteEncoding.littleEndian
    (((JFx_DataPublic00.bytes.drop 1664).drop 144).take 4) : M) = 77
  rw [List.drop_drop]
  exact congrArg (fun n : Nat => (n : M)) PV_2TNV_ByteEncoding.asset_value
theorem recipient : nativePublic.recipient = some d45 := by
  change some (digest (JFx_DataPublic00.bytes.drop 1664) 152) = some d45
  rw [digest_drop]
  exact congrArg some read45
theorem change_value : nativePublic.change = d46 := by
  change digest (JFx_DataPublic00.bytes.drop 1664) 184 = d46
  rw [digest_drop]
  exact read46
theorem nextRoot : nativePublic.nextRoot = d22 := read22
'''
for i in range(20):
 s+=f'theorem frontier{i:02} : nativePublic.snapshotFrontier ⟨{i},by decide⟩ = d{i+2:02} := read{i+2:02}\n'
s+='''theorem carry : nativePublic.nextFrontier ⟨1,by decide⟩ = d24 := read24

def pair : Digest M := ![1134794151,415789335,111944968,1818281472,628958070,505282998,905808425,2134856457]

theorem output_pair : AspisR1.SpendRelation.outputPair nativePublic = some pair := by
  change Option.map (fun r => nodeCompress r nativePublic.change) nativePublic.recipient = some pair
  rw [recipient,change_value]
  change some (nodeCompress d45 d46) = some pair
  exact congrArg some R1Z.PV_RunJoin_OutputModel16.node_39
#print axioms digest_drop
#print axioms anchor
#print axioms nullifier
#print axioms asset
#print axioms recipient
#print axioms change_value
#print axioms nextRoot
#print axioms carry
#print axioms output_pair
'''
for i in range(20):s+=f'#print axioms frontier{i:02}\n'
s+='end AspisR1.PV_2TNV_PublicLiterals\n'
p=R/'lean/PV_2TNV_PublicLiterals.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
(E/'literal-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(s.encode()).hexdigest(),digests=47,uses_existing_runjoin_pair_certificate=True),indent=2)+'\n')
