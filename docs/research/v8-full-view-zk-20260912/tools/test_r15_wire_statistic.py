"""Small wire-reader controls; no proof or oracle-law claim."""
import unittest
from run_r15_controlled_host import raw_pair_statistic


def body(queries, other_column_delta=0):
    out = bytearray(697 * 16 + 76 + 22 * 621)
    for record, query in enumerate(queries):
        packed = 0
        for slot in range(4):
            for column in range(26):
                value = 10 * query + slot + 1
                if column:
                    value += other_column_delta
                packed |= value << (31 * (slot * 26 + column))
        offset = 697 * 16 + 76 + record * 621
        out[offset:offset + 403] = packed.to_bytes(403, 'little')
    return out


class WireStatistic(unittest.TestCase):
    def test_order_and_unobserved_columns_do_not_change_statistic(self):
        queries = list(range(22))
        left = raw_pair_statistic(body(queries), queries)
        for ordering in [queries[::-1], queries[11:] + queries[:11]]:
            self.assertEqual(raw_pair_statistic(body(ordering, 7654321), ordering), left)

    def test_exact_slot_major_values(self):
        coefficients = [1508290849, 1480589898, 639192798, 666893749, 2147483646, 0, 1, 0]
        values = [41, 42, 43, 44, 61, 62, 63, 64]
        expected = sum(a * b for a, b in zip(coefficients, values)) % (2 ** 31 - 1)
        self.assertEqual(raw_pair_statistic(body(list(range(22))), list(range(22))), expected)


if __name__ == '__main__':
    unittest.main()
