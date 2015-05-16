from unittest import TestCase
from src.parser import code_gen
from src.parser import p_c

__author__ = 'joanna'


class TestCode_gen(TestCase):

    def setUp(self):
        print "test code gen before"

    def tearDown(self):
        print "done"

    def test_sod_two(self):
        print "test_sod_two"
        s = p_c.p_c().main("Tasks: 't1', 't2', 't3'; Users: 'u1', 'u2', 'u3'; SoD: ('t1','t2'), ('t2', 't3');")
        self.assertEqual(s, "sat")

    def test_fail_sod(self):
        print "test_fail_sod"
        s = p_c.p_c().main("Tasks: 't1', 't2'; Users: 'u1'; SoD: ('t1','t2');")
        self.assertEqual(s, "unsat")

    def test_sod_three(self):
        print "test_sod_three"
        s = p_c.p_c().main("Tasks: 't1', 't2', 't3'; Users: 'u1', 'u2', 'u3'; SoD: ('t1','t2'), ('t2', 't3'), ('t1', 't3');")
        self.assertEqual(s, "sat")