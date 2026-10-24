"""Tiny synthetic filesystem fixtures; no builds, Lean or extraction."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('reservation', Path(__file__).with_name('reservation.py'))
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)


class ReservationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root/'cgroup.subtree_control').write_text('memory')

    def group(self, path, cap='max', live=True, direct=True, current=17):
        p = self.root/path
        p.mkdir(parents=True, exist_ok=True)
        values = {'memory.max': cap, 'memory.high':'max', 'memory.swap.max':0,
                  'memory.current':current, 'pids.max':64, 'cgroup.subtree_control':'memory',
                  'cgroup.events':f'populated {int(live)}\nfrozen 0\n',
                  'cgroup.procs':'123\n' if direct else ''}
        for k,v in values.items():
            (p/k).write_text(str(v))
        return p

    def check_total(self, total):
        result = r.admission(self.root)
        self.assertNotIn('error', result)
        self.assertEqual(result['bounded_reserved_bytes'], total*r.GIB)
        return result

    def test_nested_count_once(self):
        self.group('user.slice', 12*r.GIB)
        self.group('user.slice/child.scope', 8*r.GIB)
        self.check_total(12)

    def test_all_slices_and_services(self):
        for parent in ['user.slice','system.slice','machine.slice']:
            self.group(parent, direct=False)
            self.group(parent+'/service.scope', 8*r.GIB)
        self.check_total(24)

    def test_empty_not_reserved(self):
        self.group('empty.scope', 40*r.GIB, live=False, direct=False, current=0)
        self.check_total(0)

    def test_direct_zero_child_live(self):
        self.group('parent.scope', 8*r.GIB, direct=False)
        self.group('parent.scope/child', 3*r.GIB)
        self.check_total(8)

    def test_uncapped_usage_visible(self):
        self.group('background.service', current=1234)
        result = self.check_total(0)
        self.assertEqual(result['uncapped_background'][0]['memory_current'], 1234)

    def test_missing_necessary_file_denies(self):
        p = self.group('broken.scope', 8*r.GIB)
        (p/'memory.max').unlink()
        self.assertFalse(r.admission(self.root)['allowed'])

    def test_invalid_population_denies(self):
        p = self.group('broken.scope')
        (p/'cgroup.events').write_text('frozen 0\n')
        self.assertFalse(r.admission(self.root)['allowed'])

    def test_exact_limit_denies(self):
        self.group('busy.scope', 47*r.GIB)
        self.assertFalse(self.check_total(47)['allowed'])

    def test_inconsistent_population_denies(self):
        self.group('parent', live=False, direct=False)
        self.group('parent/child', 8*r.GIB)
        self.assertFalse(r.admission(self.root)['allowed'])

    def test_disabled_controller_inherits_ancestor(self):
        parent = self.group('parent', 8*r.GIB, direct=False)
        (parent/'cgroup.subtree_control').write_text('')
        child = self.group('parent/child')
        for name in ['memory.max', 'memory.current', 'memory.high', 'memory.swap.max']:
            (child/name).unlink()
        self.check_total(8)

    def test_unreadable_inventory_denies(self):
        from unittest.mock import patch
        with patch.object(r.os, 'scandir', side_effect=PermissionError('fixture denied')):
            self.assertFalse(r.admission(self.root)['allowed'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
