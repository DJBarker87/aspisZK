import unittest
import NEW_geometry_source as s
class Geometry(unittest.TestCase):
 def test_positive(self):self.assertFalse(s.check()['composed_credit'])
 def deny(self,a,b):
  source=(s.E/'NEW_geometry.rs.txt').read_text();self.assertIn(a,source)
  with self.assertRaises((AssertionError,ValueError,KeyError)):s.check(source.replace(a,b))
 def test_reserve_size(self):self.deny('dst.reserve(5);','dst.reserve(6);')
 def test_logical_length(self):self.deny('let len=5*k;','let len=4*k;')
 def test_old_window(self):self.deny('dst[offset].0,raw[offset]','dst[offset].0,raw[0]')
 def test_capacity(self):self.deny('dst.capacity(),cap','dst.capacity(),M+1')
 def test_pointer(self):self.deny('dst.as_ptr(),p','dst.as_ptr(),core::ptr::null()')
 def test_prestate(self):self.deny('Vec::from_raw_parts(p,len,M)','Vec::from_raw_parts(p,0,M)')
 def test_domain(self):self.deny('kani::assume(k<N);','kani::assume(k==0);')
 def test_gather_order(self):self.deny('lines.push(values[4]);','lines.push(values[3]);')
 def test_back_result(self):self.deny('inverse[i]=NET_back_product(suffix,prefixes[i],','inverse[i]=NET_back_product(suffix,flat[i],')
 def test_written_static(self):self.deny('use super::*;','use super::*; static mut BAD:u32=0;')
if __name__=='__main__':unittest.main()
