from unittest import TestCase
from src.parser import p_c

__author__ = 'joanna'


class Test_or_execution(TestCase):

    def setUp(self):
        print "test or execution"

    def test_or(self):
        s = p_c.p_c().main("Tasks: 't0', 't1', 't2', 't3'; Users: 'u1'; Before: ('t0', 't1'), ('t0', 't2'), ('t1', 't3'), ('t2', 't3'); SoD: ('t1', 't2'); Execution: Or('t0', ['t1', 't2']);")
        self.assertEqual(s, "sat")