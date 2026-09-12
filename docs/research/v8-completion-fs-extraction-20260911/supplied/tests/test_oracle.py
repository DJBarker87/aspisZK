import unittest
from aspis_completion.oracle import *
from aspis_completion.trace_schema import *
from aspis_completion.forks import *

class OracleTests(unittest.TestCase):
    def oracle(self):
        return LazyOracle(concrete_sha256,max_fresh=100,max_calls=100)
    def test_cache_and_roles(self):
        ro=self.oracle();a=ro.query(b'x','gamma');b=ro.query(b'x','rho')
        self.assertEqual(a,b); self.assertEqual(ro.freeze().fresh_calls,1)
        self.assertFalse(ro.freeze().events[1].fresh)
    def test_resume_keeps_prefix(self):
        ro=self.oracle();ro.query(b'x');prefix=ro.freeze()
        other=LazyOracle.resume(prefix,lambda _:b'\xff'*32,max_fresh=100,max_calls=100)
        self.assertEqual(other.query(b'x'),concrete_sha256(b'x'))
        self.assertEqual(other.query(b'y'),b'\xff'*32)
        self.assertTrue(other.freeze().extends(prefix))
    def test_frozen_missing(self):
        ro=self.oracle();ro.query(b'x');frozen=FrozenAccess(ro.freeze(),2)
        self.assertEqual(frozen.lookup(b'x'),concrete_sha256(b'x'))
        with self.assertRaises(MissingAnswer): frozen.lookup(b'y')
        with self.assertRaises(BudgetExceeded): frozen.lookup(b'x')
    def test_limits(self):
        ro=LazyOracle(concrete_sha256,max_fresh=1,max_calls=2)
        ro.query(b'x');ro.query(b'x')
        with self.assertRaises(BudgetExceeded): ro.query(b'x')
        ro=LazyOracle(concrete_sha256,max_fresh=1,max_calls=3);ro.query(b'x')
        with self.assertRaises(BudgetExceeded):ro.query(b'y')
    def test_illegal_reprogramming(self):
        events=(Event(0,b'x',b'0'*32,True,'a'),Event(1,b'x',b'1'*32,False,'a'))
        with self.assertRaises(OracleError):validate_events(events)
    def test_wrong_fresh_flag(self):
        with self.assertRaises(OracleError):validate_events((Event(0,b'x',b'0'*32,False,'a'),))
    def test_phase_order(self):
        ro=self.oracle()
        for i in range(8):ro.query(bytes([i]))
        a,b=phase_prefixes(ro.freeze(),2,5,2,5)
        self.assertEqual((a.calls,b.calls),(2,5))
        with self.assertRaises(OracleError):phase_prefixes(ro.freeze(),4,3,2,5)
    def test_alias_metadata_not_separation(self):
        ans=concrete_sha256(b'ab')
        items=(Receipt(0,'gamma',(b'a',b'b'),ans,()),Receipt(1,'rho',(b'ab',),ans,(0,)))
        prefix=validate_receipts(items,check_concrete_sha=True)
        self.assertEqual(prefix.fresh_calls,1)
        self.assertEqual(cross_role_aliases(items),[(0,1)])
    def test_future_dependency(self):
        with self.assertRaises(OracleError):
            validate_receipts((Receipt(0,'x',(b'x',),b'0'*32,(0,)),))
    def test_collision(self):
        items=(Event(0,b'x',b'0'*32,True,'x'),Event(1,b'y',b'0'*26+b'1'*6,True,'x'))
        self.assertTrue(digest_collision(items))
        self.assertFalse(digest_collision(items,32))
    def test_fork_collector_retains_failures(self):
        p=Prefix(());other=Prefix((Event(0,b'x',b'0'*32,True,'x'),))
        rs=(ForkReceipt(1,p,10,8,'USEFUL',b'a'),ForkReceipt(2,p,7,3,'ABORT',None),
            ForkReceipt(3,other,20,4,'USEFUL',b'b'))
        result=collect(rs,p,2,100)
        self.assertFalse(result.enough);self.assertEqual(result.total_replay_calls,37)
        self.assertEqual(len(result.receipts),3);self.assertEqual(len(result.usable),1)
        with self.assertRaises(ValueError):collect(rs,p,2,36)
