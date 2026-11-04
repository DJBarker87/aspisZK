"""Full raw getter domain; pinned actual native methods, no canonical-only construction."""
import NFD_validate as v
from NFD_native_checks import native
from NFD_composition_support import source,structural
E=v.E
LIMBS='crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs'
TAG='crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag'
DIGESTS={'NFD_K127': 'c9bd75f2032cbea33973c973ffbede7bd4308e63765a5097d82d8937a096b5b9', 'NFD_K128': '442cd98d80ed6d1f564f5347bf65541bb157103c92041d14d6e0becb25305249', 'NFD_K129': '3a0e0d902b96e2ea6c6bf35f23f3970c6aa104079d9ca6f020e3473f7d6b1950', 'NFD_K130': 'f31161ab49829d0bd7225fa4c699bf4f8f560b44914b149cbc29ed3774aea07e', 'NFD_K131': 'c3a7d870b735ed71fea2e83533d41034d8122690639430de77501fc2f3aff2a3', 'NFD_K132': '9fe5c8506a4cc287e789741d3c3bca359c188d94adbdb89294656b08351e1f07', 'NFD_K133': '02b465aa6520a0646d6d2ad964574ec5e3a5c8dd5bba6491a7bf1df79a09eb89'}
THMS={LIMBS:['NFD_RawCarriers.raw_roundtrip','NFD_RawCarriers.limbs_result_state_effects'],TAG:['NFD_RawCarriers.tag_roundtrip','NFD_RawCarriers.tag_result_state_effects']}
CLASS='unrestricted raw eight-word carrier bijection / exhaustive three-constructor enum carrier; actual frozen pure native getter; unchanged state and empty ordered effects'
def check(c,base):
 f=c['subject'];assert f in [LIMBS,TAG]
 attempts=['NFD_K127','NFD_K128'] if f==LIMBS else ['NFD_K129','NFD_K130']
 domain='every raw eight-u32 WideExact carrier; no canonicality restriction' if f==LIMBS else 'all three Variant constructors'
 assert c['native_certificate']==dict(function=f,complete=True,domain=domain,pairs=[attempts])
 for a,positive in zip(attempts,[True,False]):
  snap=native(a,positive);m=v.read(E/(a+'-shape.json'));s=source(snap['NFD_native_contracts.patch'],'NFD_raw')
  assert s==m['source'] and v.sha(s.encode())==DIGESTS[a]
  assert m['shape']==('limbs' if f==LIMBS else 'tag') and m['mode']==('positive' if positive else 'value')
  if f==LIMBS:
   assert m['domain']=='all eight raw u32 words, no canonicality restriction'
   assert 'WideExact{c0:QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}},c1:QM31{c0:CM31{a:M31(w[4]),b:M31(w[5])},c1:CM31{a:M31(w[6]),b:M31(w[7])}}}' in snap['NFD_native_contracts.patch']
   assert 'from_limbs' not in s and 'words:[u32;8]=kani::any()' in s
 return structural(c,f,THMS[f],base,attempts,['NFD_RAW_SOURCE_DIGESTS.json'],CLASS)
