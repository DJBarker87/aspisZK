"""Offline boundary checks and exact future ordering; never a kernel backend."""
from SbfSeal_setup import require, Denied

ORDER = (
    'fresh-host-prospective', 'new-exact-scope', 'fresh-host-inside',
    'actual-host-ancestry', 'unshare-mount-net-pid', 'fork-pid-child-parent-wait',
    'verify-changed-mount-net-pid', 'private-propagation',
    'exclusive-root-safe-ancestry', 'finite-copy-hash-seal', 'readonly-root-view',
    'finite-writable-tmp', 'private-proc', 'minimal-devices',
    'public-stdio-close-other-fds', 'chroot-by-fd-close-rootfd',
    'drop-groups-bounding-ambient-gid-uid-capset-nnp', 'verify-guest',
    'exec-fixed-python', 'verify-postexec', 'parent-wait-collect-public')


def check_guest(observed, expected):
    """Synthetic metadata validator only. No Linux observation has been made.

    `expected` must ultimately come from pinned actual host/guest observations,
    not a caller-selected declaration. This function does not authorize exec.
    """
    require(set(observed) == {'abi','namespaces','uid','gid','groups','caps','nnp',
                              'fds','cgroup','root_inode','mounts','limits'}, 'guest observation schema')
    require(observed['abi'] == 'linux-x86_64-capv3', 'unsupported syscall/cap ABI')
    require(observed['uid'] == observed['gid'] == [1000]*3 and observed['groups'] == [], 'guest IDs')
    require(observed['caps'] == dict(Inh=0,Prm=0,Eff=0,Bnd=0,Amb=0), 'guest caps')
    require(type(observed['nnp']) is int and observed['nnp'] == 1, 'NNP')
    require(observed['fds'] == [0,1,2], 'surviving descriptor; no fd3 exception')
    require(observed['cgroup'] == expected['cgroup'], 'guest cgroup drift')
    require(observed['root_inode'] == expected['root_inode'], 'chroot inode mismatch')
    require(set(observed['namespaces']) == {'mnt','net','pid'}, 'namespace schema')
    for ns in ('mnt','net','pid'):
        require(observed['namespaces'][ns] == expected['guest_ns'][ns] and
                observed['namespaces'][ns] != expected['host_ns'][ns], 'namespace unchanged/wrong')
    require(observed['mounts'] == expected['mounts'] and expected['mounts'], 'exact mount view')
    require(observed['limits'] == {'nofile':[256,256], 'fsize':[16384,16384]}, 'guest limits')
    return {'authorized':False, 'status':'SYNTHETIC METADATA CONSISTENT ONLY'}


def linux_setup():
    # No mount via raced names or /proc/fd magic accepted without reviewed ABI.
    # New mount API/move_mount with empty-path descriptors is a possible future
    # backend, but flags/syscalls/proc/dev/RO topology have not been validated.
    raise Denied('Linux backend unsupported: fd-target mount ABI/private proc/dev/RO '
                 'view/chroot/drop verification and finite runtime closure need separate review/probe')
