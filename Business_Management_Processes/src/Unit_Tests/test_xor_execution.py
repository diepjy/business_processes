from unittest import TestCase
from src.parser import p_c

__author__ = 'joanna'


class Test_xor_execution(TestCase):
    pass

    def setUp(self):
        "Test xor execution"

    def test_xor(self):
        s = p_c.p_c().main("Tasks: 't0', 't1', 't2', 't3'; Users: 'u1'; Before: ('t0', 't1'), ('t0', 't2'), ('t1', 't3'), ('t2', 't3'); SoD: ('t1', 't2'); Execution: Or('t0', ['t1', 't2', 't3']), Xor('t0', ['t1', 't2']);")
        self.assertEqual(s, "sat")

    def test_xor_or(self):
        s = p_c.p_c().main("Tasks: 't0', 't1', 't2', 't3'; Users: 'u1'; Before: ('t0', 't1'), ('t0', 't2'), ('t1', 't3'), ('t2', 't3'); SoD: ('t1', 't2'); Execution: Xor('t0', ['t1', 't2']);")
        self.assertEqual(s, "sat")