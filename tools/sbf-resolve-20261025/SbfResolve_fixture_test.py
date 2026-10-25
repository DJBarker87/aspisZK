import importlib.util,pathlib,json,resource,time,hashlib
p=pathlib.Path(__file__).with_name('SbfResolve_host.py');sp=importlib.util.spec_from_file_location('host',p);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);t=time.monotonic()
q=pathlib.PurePosixPath
assert m.fixture_allowed(q('ed25519-1.5.3/tests/examples/pkcs8-v1.pem'),'a')
assert m.fixture_allowed(q('openssl-0.10.81/test/key.pem'),'a')
assert not m.fixture_allowed(q('some-package/user/key.pem'),'a')
assert not m.fixture_allowed(q('ring-0.17.14/src/rsa/signature_rsa_example_private_key.der'),'wrong checksum')
assert not m.fixture_allowed(q('task-wallet.json'),'a')
assert m.fixture_allowed(q('untrusted-0.9.0/mk/llvm-snapshot.gpg.key'),'8ecb6da28b8a351d773b68d5825ac39017e680750f980f3a1a85cd8dd28a47c1')
assert not m.fixture_allowed(q('untrusted-0.9.0/mk/llvm-snapshot.gpg.key'),'wrong checksum')
assert m.fixture_allowed(q('winapi-i686-pc-windows-gnu-0.4.0/lib/libwinapi_mincore-api-ms-win-security-credentials-l1-1-0.a'),'ac3b87c63620426dd9b991e5ce0329eff545bccbbb34f3be09ff6fb6ab51b7b6')
assert not m.fixture_allowed(q('winapi-i686-pc-windows-gnu-0.4.0/lib/credentials.json'),'ac3b87c63620426dd9b991e5ce0329eff545bccbbb34f3be09ff6fb6ab51b7b6')
u=resource.getrusage(0);r=dict(checks=9,exit=0,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),print_axioms='N/A',compiler_executions=0)
pathlib.Path('evidence/sbf-resolve-20261025/SbfResolve-fixture-tests.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
