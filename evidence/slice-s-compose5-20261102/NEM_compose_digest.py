from pathlib import Path
import sys,json,subprocess
from NEM_artifacts import ref,theorem,native_support
from NEM_install import install
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose4-20261101'
f='crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical'
j=json.loads((E/'NEM_K004-digest-call.json').read_text())
ts=[theorem('NEM_DigestInstance','next_call'),theorem('NEM_DigestInstance','result_and_frame'),theorem('NEL_DigestLoopFrame','step_and_bytes',P)]
q=dict(function=f,method='rule B: native Enumerate and same-call byte step; accepted suffix induction',all_raw_words=True,arbitrary_prestate=True,empty_external_modifies=True,trust_classification='P6/D188 option A reclassification',no_new_trust_rows=True,native_pairs=[['NEM_K002','NEM_K003'],['NEM_K004','NEM_K005']],native_support=native_support(['NEM_K002','NEM_K003','NEM_K004','NEM_K005']),frozen_body=j['frozen_body'],frozen_body_sha256=j['frozen_body_sha256'],theorems=ts,invariant='count=index; suffix=d[index..]; 0<=index<=8; arbitrary output; eight-index decreasing induction')
install(f,'digest_composition',q,ts,[ref(E/a/'receipt.json') for a in ['NEM_K002','NEM_K003','NEM_K004','NEM_K005']],ts[:1],ts[1:],'Actual frozen digest.iter().enumerate(): count=index, same borrowed M31 at d[index], exact serialization argument, one KMX indexed copy step over the same prestate, arbitrary output-cell observation and external frame. Accepted suffix induction composes these steps; M31 serializer is already composed on all raw u32 inputs. Alternative WideExact call is independently resolved by NEL. Pure fixed32 result has empty external modifies and serializer calls have no external effects. This is P6/D188 option A reclassification.',skip=['crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes'])
