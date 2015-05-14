__author__ = 'joanna'

import unittest
from src.parser import code_gen
class Basic_tasks_users(unittest.TestCase):

    # preparing to test
    def setUp(self):
        self.smt_code_gen = code_gen.code_gen()

    def tearDown(self):
        self.smt_code_gen = None

    def test_tasks_and_users(self):
        s = self.smt_code_gen.get_smt("Tasks: 't1', 't2'; Users: 'u1', 'u2';")
        self.assertEqual(s, [])

    def test_tasks_before(self):
        s = self.smt_code_gen.get_smt("Tasks: 't1', 't2'; Users: 'u1'; Before: ('t1', 't2');")
        self.assertEqual(s, [])

    def test_tasks_before_copy(self):
        s = self.smt_code_gen.get_smt("Tasks: 't1', 't2'; Users: 'u1'; Before: ('t1', 't2');")
        self.assertEqual(s, [])