"""Non-authorizing projection of the ACTUAL ResourceRssGO report shape.

No scanner, subprocess, process inspection, policy execution or privileged code.
A compact projection is data, not a fresh admission receipt. The old producer
only launches a marker; it has no reviewed helper continuation. Never accepts
an invented {'allowed': True}, guest PID, old unit, or caller freshness boolean.
"""
import json
from SbfSeal_setup import Denied, require, digest

PRODUCER_PIN = {'sha256': 'b3b6aa333cc024fa6b189e80dfde372a3ce399a62b4de3707869f267b84ed26b', 'size': 15668}
MAX_REPORT = 32*2**20  # Old read_regular's 1MB bound cannot read ~16MB reports.
EXPECTED = dict(high=3*2**30, cap=4*2**30, swap_max=0, tasks_max=64)
UNIT = 'SbfSeal-20261025-probe-v1.scope'
EPOCH = 'SbfSeal-20261025-probe-v1'
# Literal proposal, NOT a launcher. Old epoch/unit/manifest never reused.
SCOPE_ARGV = ('/usr/bin/systemd-run','--user','--scope',
              '--unit=SbfSeal-20261025-probe-v1','-p','MemoryHigh=3G',
              '-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64',
              '/usr/bin/env','-i','PATH=/usr/bin','LC_ALL=C','HOME=/probe',
              '/usr/bin/python3','-I','-S','-B',
              '/var/lib/SbfSeal-20261025-producer/SbfSeal_producer.py','inside')
# This producer file DOES NOT exist and is deliberately not an arbitrary argv.
# Next review must replace the marker route in a separately allocated producer
# job, not adopt the current offline evaluator as launch authority.


def no_duplicates(items):
    value = {}
    for key, item in items:
        require(key not in value, 'duplicate JSON key')
        value[key] = item
    return value


def parse_report(raw):
    require(type(raw) is bytes and 0 < len(raw) <= MAX_REPORT, 'full report bound')
    try:
        value = json.loads(raw, object_pairs_hook=no_duplicates,
                           parse_constant=lambda _: (_ for _ in ()).throw(Denied('nonfinite JSON')))
    except (ValueError, UnicodeError, RecursionError) as exc:
        raise Denied('invalid full report') from exc
    require(type(value) is dict and set(value) == {'api_version','collector_pid','decision',
                                                'snapshots','original_legacy','print_axioms'},
            'actual ResourceRssGO report keys')
    require(value['api_version'] == 'ResourceRssGO20261025-v1', 'actual producer schema')
    require(type(value['collector_pid']) is int and value['collector_pid'] > 1, 'host collector PID')
    require(type(value['decision']) is dict and value['decision'].get('schema') ==
            'ResourceStability20261025-v1', 'actual policy schema')
    require(type(value['decision'].get('allowed')) is bool, 'decision type')
    require(type(value['snapshots']) is dict, 'snapshot object')
    require(set(value['snapshots']) == {'before','after'}, 'full ordered snapshots')
    require(type(value['original_legacy']) is dict, 'full original visibility')
    return value


def project(raw, producer_pin):
    """Exact raw bytes retained by hash+size; pins are reviewed immutable inputs.

    Does not recompute policy and CANNOT be used by privileged_entrypoint.
    Caller supplied pin equality is only an offline comparison, never provenance.
    This separation is intentional until a current producer route is reviewed.
    """
    require(producer_pin == PRODUCER_PIN and type(producer_pin) is dict and
            set(producer_pin) == {'sha256','size'}, 'producer pin mismatch')
    report = parse_report(raw)
    decision = report['decision']
    phase = decision.get('phase')
    require(phase in ('prospective','inside-scope'), 'phase')
    require(decision.get('allowed') is True and 'error' not in decision and
            'collection_failures' not in decision, 'producer denied/unknown')
    require(decision.get('additional_bytes') == (4*2**30 if phase == 'prospective' else 0),
            'count scope once')
    identities = []
    for label in ('before','after'):
        snap = report['snapshots'][label]
        require(type(snap) is dict and type(snap.get('rows')) is list and snap['rows'], 'missing full tree')
        observed = snap.get('self_observation')
        require(type(observed) is dict and set(observed) ==
                {'pid','starttime','unified_path','path','reads'}, 'actual self observation')
        ident = {k:v for k,v in observed.items() if k != 'reads'}
        require(type(ident['starttime']) is int and ident['starttime'] > 0 and
                ident['pid'] == report['collector_pid'], 'actual host identity')
        require(ident['path'] == '/sys/fs/cgroup'+ident['unified_path'] and
                ident['unified_path'].startswith('/'), 'actual cgroup path')
        identities.append(ident)
    require(identities[0] == identities[1] == decision.get('collector_identity'), 'collector drift')
    if phase == 'inside-scope':
        binding = decision.get('scope_binding')
        require(type(binding) is dict and binding.get('self_identity') == identities[0], 'inside binding')
        require(binding.get('expected_limits') == binding.get('observed_limits') == EXPECTED,
                'exact new scope caps')
        require(identities[0]['path'].split('/')[-1] == UNIT, 'old/wrong unit')
        require(type(binding.get('ancestor_limits')) is list and binding['ancestor_limits'], 'ancestors missing')
        require(type(binding.get('finite_frontier_association')) is str, 'count-once coverage missing')
    else:
        require(decision.get('expected_limits') is None, 'prospective scope declaration')
    return dict(schema='SbfSeal-report-projection-v1', raw_report=digest(raw),
                producer=producer_pin, phase=phase, collector=identities[0],
                scope_binding=decision.get('scope_binding'),
                authorized=False, status='OFFLINE PROJECTION ONLY; policy/provenance not replayed')


def check_ancestry(before, after, projection, executable_pins):
    """Pure bounded MODEL; inputs must later be actual HOST proc observations.

    sudo may insert a monitor. Only these two explicit shapes are modelled.
    No reparent, shell, daemon, namespace PID or ambiguous identity fallback.
    Does not collect observations or establish identity-stable cancellation.
    """
    require(before == after, 'host lineage/starttime/control drift')
    roles = tuple(n.get('role') for n in before)
    require(roles in (('collector','sudo','helper'),
                      ('collector','sudo','sudo-monitor','helper')), 'unsupported sudo ancestry')
    require(set(executable_pins) == set(roles), 'all executable pins required')
    seen = set()
    for i, node in enumerate(before):
        require(set(node) == {'role','pid','ppid','starttime','cgroup','exe','uid','gid','caps'},
                'complete host process observation')
        require(type(node['pid']) is int and node['pid'] > 1 and node['pid'] not in seen and
                type(node['starttime']) is int and node['starttime'] > 0, 'host process identity')
        seen.add(node['pid'])
        require(node['exe'] == executable_pins[node['role']], 'actual executable drift')
        require(node['cgroup'] == projection['collector']['unified_path'], 'scope escape')
        if i:
            require(node['ppid'] == before[i-1]['pid'], 'broken actual parent chain')
        require(node['uid'] == node['gid'] == ([1000]*3 if i == 0 else [0]*3), 'host credentials')
        caps = node['caps']
        require(type(caps) is dict and set(caps) == {'Inh','Prm','Eff','Bnd','Amb'} and
                all(type(v) is int and 0 <= v < 2**64 for v in caps.values()), 'host capability ABI')
        require(caps['Amb'] == caps['Inh'] == 0, 'host ambient/inheritable capabilities')
        if i == 0:
            require(caps['Prm'] == caps['Eff'] == 0, 'collector elevated')
        else:
            # CAP_SYS_ADMIN(21), SYS_CHROOT(18), SETUID(7), SETGID(6), SETPCAP(8).
            needed = sum(1 << bit for bit in (21,18,7,6,8))
            require(caps['Eff'] & needed == needed and caps['Prm'] & needed == needed,
                    'missing setup capability')
    require(before[0]['pid'] == projection['collector']['pid'] and
            before[0]['starttime'] == projection['collector']['starttime'], 'report/collector mismatch')
    return dict(authorized=False, status='MODEL ONLY: bounded host ancestry consistent')


def fresh_host_admission():
    raise Denied('No reviewed current producer continuation: marker-only f29c3e0e8c/468 '
                 'failed before GO; RLIM_INFINITY portability repair separately pending; '
                 'no fresh scan/epoch/allocation/actual host ancestry/runtime pins')
