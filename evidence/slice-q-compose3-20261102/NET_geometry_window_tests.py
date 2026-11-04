import unittest
import NET_geometry_window_source as s
class Window(unittest.TestCase):
 def test_positive(self):self.assertTrue(s.check_window()['one_native_iteration'])
 def deny(self,a,b):
  code=(s.E/'NET_geometry.rs.txt').read_text();self.assertIn(a,code)
  with self.assertRaises((AssertionError,ValueError)):s.check_window(code.replace(a,b))
 def test_value(self):self.deny('dst.push(src[i]);','dst.push(src[0]);')
 def test_cursor(self):self.deny('let i=i+1;','let i=i+2;')
 def test_reserve(self):self.deny('dst.reserve(5);','dst.reserve(6);')
 def test_type(self):self.deny('src:&[M31;5]','src:&[M31;4]')
 def test_inner_domain(self):self.deny('kani::assume(t<5);let len=5*k+t;','kani::assume(t<6);let len=5*k+t;')
if __name__=='__main__':unittest.main()
