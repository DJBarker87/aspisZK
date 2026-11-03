from pathlib import Path
import subprocess,hashlib
from NEQ_install import install
from NEQ_artifacts import ref,theorem,native_support
import NEQ_unwrap_checks as u
import NEQ_common_decode_checks as d
E=Path(__file__).resolve().parent;R=E.parent.parent
for checker,field in [(u,'unwrap_conversion'),(d,'common_decode')]:
 f=checker.F;source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f.split('::')[0]],cwd=R,text=True)
 if field=='unwrap_conversion':a=source.index('pub(crate) fn unwrap_fixed_slice')
 else:a=source.index('fn decode_common(')
 z=source.index('\n}',a)+2;b=source[a:z];ts=[theorem(*n.rsplit('.',1)) for n in checker.THEOREMS];attempts=sorted({a for p in checker.PAIRS for a in p});native=native_support(attempts)
 if field=='unwrap_conversion':
  manifests=[ref(E/(a+('-unwrap-borrow.json' if a in ['NEQ_K106','NEQ_K107'] else '-unwrap.json'))) for a in attempts]
  q=dict(function=f,pairs=u.PAIRS,method='uniform generic Copy match; actual fixed-byte owned and borrowed caller instances; derived Ok conversions',domain='generic Copy success payload; actual callers derive fixed-width Ok; Err panic model retained, no new native Err credit',inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',native_support=native,theorems=ts,manifests=manifests,frozen_body=b,frozen_body_sha256=hashlib.sha256(b.encode()).hexdigest(),empty_external_modifies=True,same_owned_or_borrowed_carrier=True,ordered_effects=[])
  why='Uniform frozen generic Copy Result match; caller widths4/8/32 and actual borrowed32 places are checked natively with failing controls under KMX. NBG generic Ok and Err model laws are reused, not reproved. Native Err/panic is not newly credited: actual fixed-window callers derive successful conversion from source geometry using fixed_read_packet. All success payloads keep their same carrier and value; immutable data and direct Copy return preserve external state. P6/D188 option A is reclassification.'
 else:
  q=dict(function=f,pairs=d.PAIRS,method='ruling y exact frozen caller and complete same-record field/frame substitution',domain='every typed216-byte input, arbitrary raw words, complete rejected and returned Common records',inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',native_support=native,theorems=ts,manifests=[ref(E/(a+'-common-decode.json')) for a in attempts],frozen_body=b,frozen_body_sha256=hashlib.sha256(b.encode()).hexdigest(),full_Result=True,empty_external_modifies=True,ordered_effects=[],same_borrowed_digest_places=True)
  why='Exact erasure restores the entire frozen decode_common body. Native checks bind both borrowed digest windows to the same original216-byte allocation, every returned key byte/limb/sequence/asset field, arbitrary full child Results and stopped error prefix. Asset rejection precedes every child call. Fixed conversions derive Ok from their source bounds; the two digest children take all raw32 bytes, and validate_common receives the same complete constructed record. Concrete run substitution closes all inner laws with already CLOSED children and retains external state/effects. P6/D188 option A is reclassification.'
 install(f,field,q,ts,native,ts,ts,why)
