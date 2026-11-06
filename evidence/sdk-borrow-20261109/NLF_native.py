from NLF_formal import *
import base64

def native(a,target):
    frozen=json.loads(lzma.decompress((E/'NLF_FROZEN_INPUTS.json.xz').read_bytes()))
    lib=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/lib.rs']).decode()
    lib='#![cfg_attr(kani,feature(allocator_api))]\n'+lib+'\n#[cfg(kani)]\n#[path="NLF_sdk.rs"]\nmod NLF_sdk;\n'
    patch=frozen['NLF_KMX_copy_stubs.patch']
    files={'NLF_src/programs/r1-cost-probe/src/lib.rs':lib,
      'NLF_src/programs/r1-cost-probe/src/NLF_sdk.rs':''.join(l[1:] for l in (E/'NLF_native_packets.patch').read_text().split('+++ b/programs/r1-cost-probe/src/NLF_sdk.rs\n',1)[1].splitlines(True) if l.startswith('+')),
      'NLF_gate.py':(E/'NLF_gate.py').read_text(),'NLF_expected_KMX.patch':patch}
    env=json.loads((E.parent/'entry-sdk-20261108/NJN_K032.json').read_text())['env']
    env.update(TMPDIR=B+'/NLF_tmp',CARGO_TARGET_DIR=B+'/NLF_target',CARGO_NET_OFFLINE='true')
    cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NLF_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NLF_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
    config=dict(native_command=cmd,root_package='aspis-r1-cost-probe-program')
    # The unchanged scope runner runs the owned strict gate. Its config is a source input.
    files['NLF_native_config.json']=json.dumps(dict(attempt=a,**config))
    rc=run(a,'kani',target,command=['python3','NLF_gate.py','NLF_native_config.json'],extra=files,env_extra=env)
    log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
    assert 'Checking harness '+target in log, 'STOP queue: compile/preflight rejection; inspect before next launch'
    assert 'VERIFICATION:-' in log, 'STOP queue: no final native verdict; isolate before another launch'
    return rc
if __name__=='__main__':native(*sys.argv[1:])
