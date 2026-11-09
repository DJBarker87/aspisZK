#!/usr/bin/env python3
import json,hashlib,sys
sys.dont_write_bytecode=True
d='/tmp/p4c_nt/x/'
sh=lambda p:hashlib.sha256(open(p,'rb').read()).hexdigest()
spec=dict(run='PCWC_T001',spec_id='tool-build-aeneas-b59d5188',image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7',
 upload={'aeneas-exact-source.tar.gz':'tool_inputs/aeneas-exact-source.tar.gz','charon-exact-source.tar.gz':'tool_inputs/charon-exact-source.tar.gz','build-aeneas.sh':'tool_inputs/build-aeneas.sh'},
 archives={'aeneas':dict(upload='aeneas-exact-source.tar.gz',sha256='946d65f31e14d65efdbad996d4f706a612fcc62b2a35331fa9e2d525c596e988'),
           'charon':dict(upload='charon-exact-source.tar.gz',sha256='d8e799da5e85805ae21798bb19ed93f8a0d1a295cc3d82047c62b85d51dc92e8')},
 script=dict(upload='build-aeneas.sh',sha256='e26dd4a951748219d962dedd4d8fa5e052c92c0a8b6cb41fd31bec3b5b561e40'),
 expected_binary_sha256='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3')
json.dump(spec,open('PCWC_T001_spec.json','w'),indent=1)
