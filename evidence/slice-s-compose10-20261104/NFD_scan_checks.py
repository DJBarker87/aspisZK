"""Receipt/source audit of scanner SUPPORT ONLY cuts; never promotes a row."""
import json,subprocess
import NFD_validate as v
from NFD_native_checks import native
from NFD_composition_support import source
from NFD_bridge_checks import REV
E=v.E
DIGESTS={'NFD_K134': '54166e048df2046123d1b3461b3a3b705cf8271bdef75415d94e11ff18b64035', 'NFD_K135': 'fb086e68a9b08d622a01ac2fbc23e56fd418df721b95c22af1ba2f3e0353df1b', 'NFD_K136': '2423441244921b1e96aa09999cbefbf693d7b1973e8059e6968aa5fc7bfabd33', 'NFD_K137': 'f5d0042bf97e96109d7485612c5e07c9af5443db72a7dccda9c5796e361fc423', 'NFD_K138': '416495d17378fc1dd9d4f0be9788a910cd6b47b4e53507f20f0decd7e0e00945', 'NFD_K139': '15a38510f7888a14a4e25e4ffe42307878e9a59d42e9fe653d54e66b54a6ea44', 'NFD_K140': '0e2f824fd8617115c3e8fb72cd0cfd9d63cba1fb34a44b13705ac9e49109c2c3', 'NFD_K141': '5afd8015dd1fdaf276398855c3ff7e0b5fb01b53787c5265ed1a352a22e1e272', 'NFD_K142': '61ac6ed9e33ca76af2208f4b3e3a65fe3739275f85018b9f84360f10f2b34966', 'NFD_K143': '7c9f9da59355d02755f663121c5d9633800cadb391b47af3116890aeaad8b1a5', 'NFD_K144': '65b4f1899d3d213b005f0760f247eb5fb5a22d477212d95de82cf113d17e4d00', 'NFD_K145': 'a8ae9273fd76cbb6e8f87ec2f6e2edecd4afd18f7f44ba5bacc52ffb92a206d3', 'NFD_K146': '709cee57b5fbb97365c0a4ce09dbf55819b7e08089fd531d5582d698727531d2', 'NFD_K147': 'f922e9a014f2ba0ff71cdf06a22342126710c21e55ed06905398647ee1660d0f', 'NFD_K148': 'e7801513b3170e923cd97bf60da8c0806577395101243e7f12506b94264bc82e', 'NFD_K149': 'e16a76bb87402756b0f05a087ee16f903142c8b38f92cd2a224af6f17a6eb7d8', 'NFD_K150': 'de09db4bf76524b8090868b3aa669a31e189b0cf8a804b5a2190f453249a6fd3'}
def audit():
 f=subprocess.check_output(['git','show',REV+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
 a=f.index('fn scan_proof_buffer(');original=f[a:f.index('\n}',a)+2];out=[]
 positive={134,136,138,140,142,146,148}
 for n in range(134,151):
  a=f'NFD_K{n:03}';snap=native(a,n in positive);m=v.read(E/(a+'-shape.json'));s=source(snap['NFD_native_contracts.patch'],'NFD_scan')
  assert s==m['source'] and v.sha(s.encode())==DIGESTS[a] and m['frozen_body']==original
  assert 'full688-byte equality-to-iteration association remains OPEN' in m['classification']
  if m['native']:assert m['native'] in s
  out.append(dict(attempt=a,shape=m['shape'],mode=m['mode'],slot=m['slot'],credited_root=False))
 return dict(cuts=out,root_status='OPEN',open_obligation='NativeEqualityAssociation for the actual688-byte standard/compiler comparison on the SAME two live buffers',new_closed_rows=0,new_closed_edges=0)
if __name__=='__main__':
 (E/'NFD_SCAN_SUPPORT_AUDIT.json').write_text(json.dumps(audit(),indent=1)+'\n');print('17 scanner cuts validated; no root credit')
