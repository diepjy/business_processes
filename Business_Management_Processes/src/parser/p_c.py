__author__ = 'joanna'

from z3 import *
from lexer_class import *
from ply.lex import lex
from ply.yacc import yacc
import itertools
import ast
from decimal import Decimal

class p_c(object):
    tokens = lexer_class.tokens

    smt_sort_task = "(declare-sort Task) \n"
    smt_sort_user = "(declare-sort User) \n"
    smt_fun_before = "(declare-fun before (Task Task) Bool) \n"
    smt_fun_seniority = "(declare-fun seniority (User User) Bool) \n"
    smt_fun_executed = "(declare-fun executed (Task) Bool)\n"
    smt_fun_duration = "(declare-fun duration (Task) Real)\n"

    smt_fun_alloc_user = "(declare-fun alloc_user (Task) User) \n"

    smt_const_bottom = "(declare-const bottom User) \n"

    smt_fun_seniority_transitivity = "(assert (forall ((u1 User) (u2 User) (u3 User)) " \
                                     "(=> (and (seniority u1 u2) (seniority u2 u3)) " \
                                     "(seniority u1 u3))" \
                                     "))\n"

    smt_before_transitivity = "(assert (forall ((t1 Task) (t2 Task) (t3 Task))" \
                              "(=>" \
                              "(and(before t1 t2) (before t2 t3))" \
                              "(before t1 t3)" \
                              ")" \
                              "))\n"

    smt_users_neq_bottom = "(assert (forall ((u User))" \
                           "(=>" \
                           "(not(= u bottom))" \
                           "(and (not(seniority bottom u)) (not(seniority u bottom)))" \
                           ")" \
                           "))\n"

    smt_non_cyclic_seniority = "(assert (forall ((u User))" \
                               "(not (seniority u u))" \
                               "))\n"

    smt_non_cyclic_before = "(assert (forall ((t Task))" \
                            "(not (before t t))" \
                            "))\n"
    bottom_user_execution_axiom = "(assert (forall ((t Task))" \
                                  "(=> " \
                                  "(executed t)" \
                                  "(not(=(alloc_user t) bottom))" \
                                  ")" \
                                  "))\n"
    not_bottom_user_execution_axiom = "(assert (forall ((t Task))" \
                                      "(=> " \
                                      "(not(executed t))" \
                                      "(=(alloc_user t) bottom)" \
                                      ")" \
                                      "))\n"

    def __init__(self):
        self.users = []
        self.tasks = []
        self.dict_eq_tasks = { }
        self.dict_gt_tasks = { }
        self.dict_lt_tasks = { }
        self.dict_neq_taks = { }
        self.dict_users = { }
        self.dict_seniority = { }
        self.dict_before = { }
        self.dict_user_alloc = { }
        self.dict_task_user_auth = { }
        self.dict_or_task = { }
        self.dict_xor_task = { }
        self.dict_sod = []
        self.dict_bod = []
        self.allocate_users = False
        self.dict_duration = {}

    def p_prog(self, p):
        '''prog : begin
        '''
        global users
        global tasks
        global dict_eq_tasks
        global dict_gt_tasks
        global dict_lt_tasks
        global dict_neq_tasks
        global dict_users
        global dict_seniority
        global dict_user_alloc
        global dict_task_user_auth
        global dict_or_task
        global dict_xor_task
        global dict_sod
        global dict_bod
        global allocate_users
        global dict_before
        global dict_duration
        users = self.users
        tasks = self.tasks
        dict_eq_tasks = self.dict_eq_tasks
        dict_lt_tasks = self.dict_lt_tasks
        dict_gt_tasks = self.dict_gt_tasks
        dict_neq_tasks = self.dict_neq_taks
        dict_users = self.dict_users
        dict_seniority = self.dict_seniority
        dict_user_alloc = self.dict_user_alloc
        dict_task_user_auth = self.dict_task_user_auth
        dict_or_task = self.dict_or_task
        dict_xor_task = self.dict_xor_task
        dict_sod = self.dict_sod
        dict_bod = self.dict_bod
        allocate_users = self.allocate_users
        dict_before = self.dict_before
        dict_duration = self.dict_duration
        print "dict gt tasks", dict_gt_tasks
        print "dict lt tasks", dict_lt_tasks
        print "dict eq tasks", dict_eq_tasks
        print "dict neq tasks", dict_neq_tasks
        print "dict neq tasks", dict_neq_tasks
        print "dict neq tasks", dict_neq_tasks
        print "dict duration", dict_duration
        print "dict seniority", dict_seniority
        print "dict sod", dict_sod
        print "dict bod", dict_bod
        print "dict user alloc", dict_user_alloc
        print "dict before", dict_before
        print "dict_duration", dict_duration
        print "dict or", dict_or_task
        print "dict xor", dict_xor_task

    def p_begin(self, p):
        '''begin : TASKS COLON task_node USERS COLON user_node
                 | TASKS COLON task_node USERS COLON user_node rules'''
        self.users.append('bottom')
        p[0] = p[3] + p[6]

    def p_rules(self, p):
        '''rules : BEFORE COLON before_task_node_pair
                 | BOD COLON bod_task_node_pair
                 | SOD COLON sod_task_node_pair
                 | SENIORITY COLON user_node_pair
                 | AUTHORISED COLON authorised_pair
                 | EXECUTION COLON fork
        '''
        p[0] = p[3]

    def p_before_task_pair(self, p):
        '''before_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA before_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        # self.dict_before[p[2].replace("'", "")] = (p[4].replace("'", "")).split(",")
        p[0] = [p[2]] + [p[4]]
        if not p[2].replace("'", "") in self.dict_seniority:
            self.dict_before[p[2].replace("'", "")] = []
            self.dict_before[p[2].replace("'", "")].append(p[4].replace("'", ""))
        else:
            self.dict_before[p[2].replace("'", "")].append(p[4].replace("'", ""))


    def p_bod_task_pair(self, p):
        '''bod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA bod_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        p[0] = [p[2]] + [p[4]]
        self.dict_bod.append([p[2].replace("'", "")] + [p[4].replace("'", "")])
        # if not p[2].replace("'", "") in self.dict_seniority:
        #     self.dict_bod[p[2].replace("'", "")] = []
        #     self.dict_bod[p[2].replace("'", "")].append(p[4].replace("'", ""))
        # else:
        #     self.dict_bod[p[2].replace("'", "")].append(p[4].replace("'", ""))

    def p_sod_task_pair(self, p):
        '''sod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA sod_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        p[0] = [p[2]] + [p[4]]
        self.dict_sod.append([p[2].replace("'", "")] + [p[4].replace("'", "")])
        # if not p[2].replace("'", "") in self.dict_seniority:
        #     self.dict_sod[p[2].replace("'", "")] = []
        #     self.dict_sod[p[2].replace("'", "")].append(p[4].replace("'", ""))
        # else:
        #     self.dict_sod[p[2].replace("'", "")].append(p[4].replace("'", ""))

    def p_user_pair(self, p):
        '''user_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                          | LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair
                          | LPAREN NODE COMMA NODE RPAREN END
                          '''
        p[0] = [p[2]] + [p[4]]
        if not p[2].replace("'", "") in self.dict_seniority:
            self.dict_seniority[p[2].replace("'", "")] = []
            self.dict_seniority[p[2].replace("'", "")].append(p[4].replace("'", ""))
        else:
            self.dict_seniority[p[2].replace("'", "")].append(p[4].replace("'", ""))

    def p_authorised_pair(self, p):
        '''authorised_pair : LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN END rules
                           | LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN COMMA authorised_pair
                           | LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN END
        '''
        p[0] = [p[2]] + [p[5]]
        # self.dict_task_user_auth[p[2].replace("'", "")] = (p[5].replace("'", "")).split(",")
        if not p[2].replace("'", "") in self.dict_seniority:
            self.dict_task_user_auth[p[2].replace("'", "")] = []
            self.dict_task_user_auth[p[2].replace("'", "")].append(p[4].replace("'", ""))
        else:
            self.dict_task_user_auth[p[2].replace("'", "")].append(p[4].replace("'", ""))

    def p_user_list(self, p):
        '''user_list : NODE COMMA user_list
                     | NODE
        '''
        if len(p) == 2:
            p[0] = p[1]
        if len(p) > 2:
            p[0] = p[1] + p[2] + p[3]

    def p_task_node(self, p):
        '''task_node : NODE end
                | NODE COMMA task_node
                | NODE variable_task_option
                '''
                # | NODE task_option'''
        p[0] = p[1]
        p_c.task = p[0]
        self.tasks.append(p[0].replace("'", ""))
        # print "p[2]", p[2]
        # print "p[1]", p[1]
        if len(p) >= 2 and p[2] != ";":
            for o in p[2]:
                # print "o is in the loop", o
                if "duration" in o:
                    # Remove duration from the options and add to duration ductionary
                    self.dict_duration[p[1].replace("'", "")] = o.replace("duration", "")
                if "=" in o and "!=" not in o:
                    self.dict_eq_tasks[p[1].replace("'", "")] = ast.literal_eval(o.replace("=", ""))
                elif ">" in o:
                    self.dict_gt_tasks[p[1].replace("'", "")] = ast.literal_eval(o.replace(">", ""))
                elif "<" in o:
                    self.dict_lt_tasks[p[1].replace("'", "")] = ast.literal_eval(o.replace("<", ""))
                elif "!=" in o:
                    self.dict_neq_tasks[p[1].replace("'", "")] = ast.literal_eval(o.replace("!=", ""))

    def p_user_node(self, p):
        '''user_node : NODE end
                | NODE COMMA user_node
                | NODE user_option
                | NODE end_rule'''
        p[0] = p[1]
        if p[0] not in self.users:
            self.users.append(p[0].replace("'", ""))

    def p_variable_task_option(self, p):
        '''variable_task_option : OPTION variable_option_flag COLON op variable_task_option
                  | OPTION variable_option_flag COLON op COMMA task_node
                  | OPTION variable_option_flag COLON op end
                  | OPTION variable_option_flag COLON time variable_task_option
                  | OPTION variable_option_flag COLON time COMMA task_node
                  | OPTION variable_option_flag COLON time end
                  '''
        if "duration" in p[2]:
            if p[5] != ";" and p[5] != ",":
                # If it's not the end of the domain of tasks and it'll recurse
                p[0] = [p[2] + p[4]] + p[5]
            elif p[5] == ";":
                # If it is the end
                p[0] = [p[2] + p[4]]
            elif p[5] == ",":
                # The case where there is a comma
                p[0] = [p[2] + p[4]]
        elif "min_sec_lv" in p[2]:
            if p[5] != ";" and p[5] != ",":
                # If it's not the end of the domain of tasks and it'll recurse
                p[0] = [p[4]] + p[5]
            elif p[5] == ";":
                # If it is the end
                p[0] = [p[4]]
            elif len(p) == 7:
                # The case where there is a comma
                p[0] = [p[4]]
        # print "length", len(p)
        # if len(p) == 7:
        #     if "duration" in p[2]:
        #         p[0] = [p[2] + p[4]]
        #     else:
        #         p[0] = [p[4]]
        # elif "duration" in p[2]:
        #     p[0] = [p[2] + p[4]] + [p[5]]
        # else:
        #     p[0] = [p[4]] + [p[5]]
        #     print "p[0] is in variable task option", p[0]

    # def p_task_option(self, p):
    #     '''task_option : OPTION option_flag task_option
    #               | OPTION option_flag COMMA task_node
    #               | OPTION option_flag end
    #               '''
    #     p[0] = p[2]

    # ie -min_sec_lv:'t4'
    def p_variable_option_flag(self, p):
        '''variable_option_flag : MIN_SEC_LV
                                | DURATION
        '''
        p[0] = p[1]

    # ie -start
    # def p_option_flag(self, p):
    #     '''option_flag : START
    #     '''
    #     p[0] = p[1]

    def p_op(self, p):
        '''op : EQ LSQPAREN task_list RSQPAREN
              | GEQ LSQPAREN task_list RSQPAREN
              | LEQ LSQPAREN task_list RSQPAREN
              | NEQ LSQPAREN task_list RSQPAREN
              '''
        p[0] = p[1] + p[2] + p[3] + p[4]

    def p_time(self, p):
        '''time : LPAREN NUMBER RPAREN'''
        p[0] = str(p[2])

    def p_execution(self, p):
        '''fork : OR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END rules
                | OR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN COMMA fork
                | OR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END
                | XOR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END rules
                | XOR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN COMMA fork
                | XOR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END
        '''
        p[0] = [p[3]] + [p[6]]
        if p[1] == "Or":
            self.dict_or_task[p[3].replace("'", "")] = (p[6].replace("'", "")).split(",")
        elif p[1] == "Xor":
            self.dict_xor_task[p[3].replace("'", "")] = (p[6].replace("'", "")).split(",")

    def p_task_list(self, p):
        '''task_list : NODE COMMA task_list
                     | NODE
        '''
        if len(p) == 2:
            p[0] = p[1]
        if len(p) > 2:
            p[0] = p[1] + p[2] + p[3]

    def p_user_option(self, p):
        '''user_option : OPTION USERS_OPTION user_option
              | OPTION USERS_OPTION COMMA
              | OPTION USERS_OPTION COLON users_global_option
              | OPTION USERS_OPTION end
              '''
        p[0] = p[1]

    def p_users_global_option(self, p):
        '''users_global_option : ALLOCATE end_rule'''
        p[0] = p[1]
        if p[0] == 'allocate':
            self.allocate_users = True

    def p_end(self, p):
        '''end : END
               | END begin
               '''
        p[0] = p[1]

    def p_end_rule(self, p):
        '''end_rule : END rules'''
        if len(p) == 0:
            p[0] = p[1]
        else:
            p[0] = p[1]

    def p_error(self, p):
        print "Syntax error in input!"
        print p

    def get_eq_task_options(self, d, task_list):
        smt_options = ""
        for key, value in d.iteritems():
            # BOD
            for t in task_list:
                if t in value:
                    smt_options += "(assert " \
                                   "(=>" \
                                   "(and (executed " \
                                   + key + \
                                   ") (executed " \
                                   + t + \
                                   "))" \
                                   "(=(alloc_user " \
                                   + key + \
                                   ") (alloc_user " \
                                   + t + \
                                   "))" \
                                   ")" \
                                   ")\n"
        return smt_options

    def get_lt_task_options(self, d, task_list):
        smt_options = ""
        for key, value in d.iteritems():
            for t in task_list:
                if t in value:
                    smt_options += "(assert " \
                                   "(=>" \
                                   "(and (executed " \
                                   + t + \
                                   ") (executed " \
                                   + key + \
                                   "))" \
                                   "(seniority (alloc_user " \
                                   + t + \
                                   ") (alloc_user " \
                                   + key + \
                                   "))" \
                                   ")" \
                                   ")\n"
        return smt_options

    def get_gt_task_options(self, d, task_list):
        smt_options = ""
        for key, value in d.iteritems():
            for t in task_list:
                if t in value:
                    smt_options += "(assert " \
                                   "(=>" \
                                   "(and (executed " \
                                   + key + \
                                   ") (executed " \
                                   + t + \
                                   "))" \
                                   "(seniority (alloc_user " \
                                   + key + \
                                   ") (alloc_user " \
                                   + t + \
                                   "))" \
                                   ")" \
                                   ")\n"
        return smt_options

    def get_neq_task_options(self, d, task_list):
        smt_options = ""
        for key, value in d.iteritems():
            for t in task_list:
                if t in value:
                    smt_options += "(assert " \
                                   "(=>" \
                                   "(and (executed " \
                                   + key + \
                                   ") (executed " \
                                   + t + \
                                   "))" \
                                   "(not(=(alloc_user " \
                                   + key + \
                                   ") (alloc_user " \
                                   + t + \
                                   ")))" \
                                   ")" \
                                   ")\n"
        return smt_options

    def executed_and_tasks(self, xor_task_list, or_task_list, task_list):
        executed_tasks = ""
        or_xor_tasks = []
        for key, value in xor_task_list.iteritems():
            or_xor_tasks += value
        for key, value in or_task_list.iteritems():
            or_xor_tasks += value
        for p in task_list:
            if p not in or_xor_tasks:
                executed_tasks += "(assert (executed " + p + "))\n"
        return executed_tasks

    def executed_or_tasks(self, or_task_list):
        or_execution = ""
        for key, value in or_task_list.iteritems():
            key_list = [key]
            or_execution += "(assert (or "
            for elem in itertools.product(key_list, value):
                or_execution += "(and (executed " + elem[0] + ") "
                or_execution += "(executed " + elem[1] + "))"
        or_execution += "))"
        return or_execution

    def executed_xor_tasks(self, xor_task_list):
        xor_execution = ""
        for key, value in xor_task_list.iteritems():
            key_list = [key]
            xor_execution += "(assert (xor "
            for elem in itertools.product(key_list, value):
                xor_execution += "(and (executed " + elem[0] + ") "
                xor_execution += "(executed " + elem[1] + "))"
        xor_execution += "))\n"
        return xor_execution

    def unique_users_axiom(self, user_list):
        c = []
        unique_users = ""
        for i in itertools.product(user_list, user_list):
            c.append(i)
        for cs in c:
            if cs[0] != cs[1]:
                # s.push()
                unique_users += "(assert (not(= " + cs[0] + " " + cs[1] + ")))\n"
        return unique_users

    def authorised_task_to_users_axiom(self, auth_list):
        auth = ""
        for key, value in auth_list.iteritems():
            auth += "(assert (or "
            for u in value:
                auth += "(=(alloc_user " + key + ")" + u +")"
            auth += "(=(alloc_user " + key +") bottom)"
            auth += "))\n"
        return auth

    def executable_sod(self, sod_list):
        sod = ""
        for p in sod_list:
            sod += "(assert (=> "
            sod += "(and (executed " + p[0] + ") (executed " + p[1] + "))"
            sod += "(not (=(alloc_user " + p[0] + ") (alloc_user " + p[1] + ")))))\n"
        return sod

    def executable_bod(self, bod_list):
        bod = ""
        for p in bod_list:
            bod += "(assert (=> "
            bod += "(and (executed " + p[0] + ") (executed " + p[1] + "))"
            bod += "(=(alloc_user " + p[0] + ") (alloc_user " + p[1] + "))))\n"
        return bod

    def only_users(self, user_list):
        only_users = "(assert (forall ((u User)) (or"
        for u in user_list:
            only_users += "(= u " + u + ")"
        only_users += ")))\n"
        return only_users

    def add_users(self, user_list):
        users = ""
        for u in user_list:
            if "bottom" != u:
                users += "(declare-const " + u + " User) \n"
        return users

    def add_tasks(self, task_list):
        tasks = ""
        for t in task_list:
            tasks += "(declare-const " + t + " Task)\n"
        return tasks

    def add_before_tasks(self, before_tasks):
        before = ""
        for t_key, t_value in before_tasks.iteritems():
            for t in t_value:
                before += "(assert (before " + t_key + " " + t + "))\n"
        return before

    def add_seniority(self, seniority_list):
        seniority = ""
        for u_key, u_value in seniority_list.iteritems():
            for u in u_value:
                seniority += "(assert (seniority " + u_key + " " + u + ")) \n"
        return seniority

    def add_duration(self, duration_list):
        duration = ""
        for task, dur in duration_list.iteritems():
            duration += "(assert (= (duration " + task + ")" + dur + "))\n"
        return duration

    def main(self, prompt_input):
        lexer = lex(module=lexer_class(), optimize=1)
        parser = yacc(module=p_c(), start='prog', optimize=1)

        s = prompt_input

        lexer.input(s)
        # for token in lexer:
        #         print(token)
        t = parser.parse(s, lexer=lexer)
        print t

        smt_output = p_c.smt_sort_task + \
            p_c.smt_sort_user + \
            p_c.smt_fun_executed + \
            p_c.smt_fun_before + \
            p_c.smt_fun_seniority + \
            p_c.smt_const_bottom + \
            p_c.smt_fun_alloc_user + \
            p_c.smt_fun_duration + \
            p_c.smt_before_transitivity + \
            p_c.smt_fun_seniority_transitivity +\
            p_c.smt_users_neq_bottom + \
            p_c.smt_non_cyclic_before + \
            p_c.smt_non_cyclic_seniority

        # Collect results to SMT solver
        original = smt_output
        original += self.add_users(users)
        original += self.add_tasks(tasks)
        f = z3.parse_smt2_string(original)
        s = z3.Solver()
        s.add(f)
        print 'Result of first check', s.check()
        m = s.model()

        auth = self.authorised_task_to_users_axiom(dict_task_user_auth)
        original += auth
        a = z3.parse_smt2_string(original)
        s.add(a)
        print "Result of authorised_task_to_users_axiom", s.check()
        s.model()

        original += self.bottom_user_execution_axiom
        original += self.not_bottom_user_execution_axiom
        bottom_user_axiom = z3.parse_smt2_string(original)
        s.add(bottom_user_axiom)
        print "after adding execution bottom axiom", s.check()
        s.model

        try:
            # Get all the before rules of the workflow
            original += self.add_before_tasks(dict_before)
            original += self.add_seniority(dict_seniority)
            original += self.add_duration(dict_duration)
            print original
            a = z3.parse_smt2_string(original)
            s.add(a)
            print "Result of before and seniority", s.check()
            s.model()

            try:
                # go through the options and check if they are possible given the basic model
                if dict_eq_tasks:
                    smt_options = self.get_eq_task_options(dict_eq_tasks, tasks)
                    original += smt_options
                if dict_lt_tasks:
                    smt_options = self.get_lt_task_options(dict_lt_tasks, tasks)
                    original += smt_options
                if dict_gt_tasks:
                    smt_options = self.get_gt_task_options(dict_gt_tasks, tasks)
                    original += smt_options
                if dict_neq_tasks:
                    smt_options = self.get_neq_task_options(dict_neq_tasks, tasks)
                    original += smt_options

                o = z3.parse_smt2_string(original)
                s.add(o)
                print "after options added check", s.check()
                s.model()

                try:
                    original += self.only_users(users)
                    o = z3.parse_smt2_string(original)
                    s.add(o)
                    print "after adding only_users axiom", s.check()
                    s.model()

                    try:
                        original += self.executable_sod(dict_sod)
                        sod = z3.parse_smt2_string(original)
                        s.add(sod)
                        print "after execution sod added check", s.check()
                        s.model()

                        try:
                            original += self.unique_users_axiom(users)
                            unique = z3.parse_smt2_string(original)
                            s.add(unique)
                            print "after options added check", s.check()
                            s.model()

                            try:
                                original += self.executed_and_tasks(dict_xor_task, dict_or_task, tasks)
                                exe_and_tasks = z3.parse_smt2_string(original)
                                s.add(exe_and_tasks)
                                print "after adding executed tasks in and", s.check()
                                s.model()

                                try:
                                    if dict_or_task:
                                        original += self.executed_or_tasks(dict_or_task)
                                        exe_or_tasks = z3.parse_smt2_string(original)
                                        s.add(exe_or_tasks)
                                        print "after adding executed tasks in or", s.check()
                                    if dict_xor_task:
                                        original += self.executed_xor_tasks(dict_xor_task)
                                        exe_xor_tasks = z3.parse_smt2_string(original)
                                        s.add(exe_xor_tasks)
                                        print "after adding executed tasks in xor", s.check()
                                except Z3Exception as e:
                                    print "fail at executed or tasks", e

                            except Z3Exception as e:
                                print "Z3 error: model not avalible after adding executed tasks in and", e

                        except Z3Exception as e:
                            print "not all input users are unique", e

                    except Z3Exception as e:
                        print "executable SOD fail", e

                except Z3Exception as e:
                    print "failed to add only_users axiom", e

            except Z3Exception as e:
                print "failed to sat with options"

        except Z3Exception as e:
            print "z3 error", e

        # Do the allocation of users and tasks if not specified
        alloc_user_task = ""
        if allocate_users:
            # Loop through all users and allocate them to a task
            # Use BOTTOM user to verify
            c = []
            for i in itertools.product(users, tasks):
                c.append(i)
            original_extra = original
            for cs in c:
                s.push()
                original_extra += "(push)\n"
                alloc_user_task = "(assert (= (alloc_user " + cs[1] + ") " + cs[0] + "))\n"
                original_extra += alloc_user_task
                e = z3.parse_smt2_string(original_extra)
                s.add(e)
                check = s.check()
                print 'result of push', check
                if check == sat:
                    m = s.model()
                elif check == unsat:
                    original_extra += "(pop)\n"
                    e = z3.parse_smt2_string(original_extra)
                    s.pop()
                    s.add(e)
                    print s.check()

        print s.check()
        print "UNSAT CORE", s.unsat_core()

        print "COMPLETION TIME"
        # completion_time = "(declare-const completion_time Real)"
        # original += completion_time
        # original += "(assert (= completion_time" \
        #                                     "(+ "
        # for t in tasks:
        #     original += "(ite (executed " + t + ") " +  + "0)"
        # brackets = ")))"

        # print "COMPLETION TIME"
        # completion_time = Real('completion_time')
        # # total_completion_time = Real('total_completion_time')
        # completion_time_model = s.model()
        # print completion_time_model
        # total_completion_time = 0
        # Task = DeclareSort('Task')
        # duration_times = []
        # for t in tasks:
        #     for ms in completion_time_model:
        #         # Get executed and duration out of the model
        #         if "executed" in str(ms) and "executed!" not in str(ms):
        #             ts = Const(str(t), Task)
        #             executed = completion_time_model.eval(ms(ts))
        #             for mss in completion_time_model:
        #                 if "duration" in str(mss):
        #                     if str(executed) == "True":
        #                         # Get the duration of the executed task and sum to total_completion_time
        #                         duration = completion_time_model.eval(mss(ts))
        #                         print duration
        #                         total_completion_time = total_completion_time + duration
        # s.add(completion_time == total_completion_time)
        # # x = Real('x')
        # # s.add(x >= 0)
        # self.worst_time_completion(completion_time, 0.001, s)
        # # self.worst_time_completion(x, 0.001, s)

        # print "ASSIGNMENT"
        #Assignment and verification of the model
        model_map_task = []
        model_map_user = []
        solution_map = []
        m = s.model()
        Task = DeclareSort('Task')
        for ms in m:
            if str(ms) in tasks:
                model_map_task.append((ms, m[ms]))
            if str(ms) in users:
                model_map_user.append((ms, m[ms]))
            str_ms = str(ms)
            if str_ms == "alloc_user":
                for model_task in model_map_task:
                    t = Const(str(model_task[0]), Task)
                    user_solution = m.eval(ms(t))
                    for model_user in model_map_user:
                        if str(model_user[1]) == str(user_solution):
                            solution_map.append((t, model_user[0]))
        print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
        print s.check()
        verified = True
        if s.check() == sat:
            verify_userlist = users[:]
            verify_userlist.remove("bottom")
            for u in itertools.product(verify_userlist, verify_userlist):
                print u
                # if dict_sod:
                verify_sod = self.verify_result_sod(original, s, u)
                if verify_sod:
                    # Don't need to do anything
                    print "VERIFIED SOD"
                else:
                    # Need to check other cases to see why it doesn't satisfy
                    print "UNVERIFIED SOD"
                verify_bod = self.verify_result_bod(original, s, u)
                if verify_bod:
                    # Don't need to do anything
                    print "VERFIFIED BOD"
                else:
                    # Need to check other cases to see why it doesn't satisfy
                    print "UNVERIFIED BOD"
                verify_seniroity = self.verify_result_seniroity(original, s, u)
                if verify_seniroity:
                    print "VERIFIED SENIORITY"
                else:
                    print "UNVERIFIED SENIORITY"
                verified_ = verify_sod and verify_bod and verify_seniroity
                print "this user pair has verification:", verified_
                verified = verified and verified_
                print verified
                print "================================================================"
        # print original
        if verified:
            final_solver = z3.Solver()
            final = z3.parse_smt2_string(original)
            final_solver.add(final)
            final_solver.check()
            self.evaluate_final_model(final_solver.model())
            print "VERIFIED!!!!!"
            if not solution_map:
                return str(s.check())
            else:
                return str(s.check()) + " " + str(solution_map).strip('[]')
        else:
            print "UNVERIFIED!!!"
            return str(unsat)

    def worst_time_completion(self, x, delta, s):
        print "worst time completion!!!"
        print x
        res = s.check()
        if res == unsat:
            return unsat
        else:
            m = s.model()
        # Finding the upper bound time
        print m
        # Unbounded search
        while res == sat:
            s.push()
            s.add(x > 2*m[x])
            res = s.check()
            if res == sat:
                m = s.model()
            s.pop()
        # Bisection
        v = m[x]
        print v
        v = float(v.as_decimal(10)[:])
        print v
        max_time = 2*v
        min_time = v
        print "max before", max_time
        print "min before", min_time
        while (max_time-min_time) > delta:
            s.push()
            s.add((((max_time - min_time)/2)+min_time) <= x)
            res = s.check()
            print "res in bisection", res
            if res == sat:
                min_time = (((max_time-min_time)/2)+min_time)
            else:
                max_time = (((max_time-min_time)/2)+min_time)
            s.pop()
        print s.check()
        print s.model()
        y = (max_time+min_time)/2
        print "max in end", max_time
        print "min in end", min_time
        print "y", y
        return y


        # Pass the model and check that it is consistent with the input
    # Sod verification: if it's the same user, should return unsat
    def verify_result_sod(self, original, s, u):
        verify_user_list = users[:]
        verify_user_list.remove("bottom")
        verify_original = original[:]
        verify = True
        s.push()
        res = s.check()
        if res == sat:
            m = s.model()
            # print m
        else:
            verify = False
            return verify
        print u
        # Task = DeclareSort('Task')
        # for t_key, t_value in dict_sod:
        #     print t_key
        #     print t_value
        #     ts_key = Const(str(t_key), Task)
        #     ts_value = Const(str(t_value), Task)
        #     for ms in m:
        #         if "alloc_user" in str(ms) and "alloc_user!" not in str(ms):
        #             print "model t_key", t_key, m.eval(ms(ts_key))
        #             print "model t_value", t_value, m.eval(ms(ts_value))
        for sod in dict_sod:
            v = z3.parse_smt2_string(verify_original)
            s.add(v)
            s.push()
            verify_original += "(push)\n"
            verify_original += "(assert (and (executed " + sod[0] +") (= (alloc_user " + sod[0] +")" + u[0] + ")))\n"
            verify_original += "(assert (and (executed " + sod[1] +") (= (alloc_user " + sod[1] +")" + u[1] + ")))\n"
            v = z3.parse_smt2_string(verify_original)
            s.add(v)
            # If they are the same user, the result should be unsat
            if u[0] == u[1]:
                if s.check() == sat:
                    # It shouldn't be sat
                    print "FAIL - unverified in equal"
                    verify = False
                    s.pop()
                    verify_original += "(pop)\n"
                else:
                    # It should be unsat
                    print "PASS - verified"
                    s.pop()
                    verify_original += "(pop)\n"
            # If they are different users, the result should be sat
            elif u[0] != u[1]:
                if s.check() == sat:
                    print "PASS - verified"
                    s.pop()
                    verify_original += "(pop)\n"
                else:
                    print "FAIL - unverified in unequal"
                    s.pop()
                    # Check why it's being unverified by checking seniority constraints
                    verify = self.verify_result_seniroity(original, s, u)
                    # verify = False
                    verify_original += "(pop)\n"
        print "verify in sod", verify
        return verify

    def verify_result_bod(self, original, s, u):
        verify_user_list = users[:]
        verify_user_list.remove("bottom")
        verify_original = original[:]
        verify = True
        s.push()
        for bod in dict_bod:
            v = z3.parse_smt2_string(verify_original)
            s.add(v)
            # for u in itertools.product(verify_user_list, verify_user_list):
            s.push()
            verify_original += "(push)\n"
            verify_original += "(assert (and (executed " + bod[0] +") (= (alloc_user " + bod[0] +")" + u[0] + ")))\n"
            verify_original += "(assert (and (executed " + bod[1] +") (= (alloc_user " + bod[1] +")" + u[1] + ")))\n"
            v = z3.parse_smt2_string(verify_original)
            s.add(v)
            # If they are different users, the result should be unsat
            if u[0] != u[1]:
                if s.check() == sat:
                    # It shouldn't be sat
                    print "FAIL - unverified"
                    verify = False
                else:
                    # It should be unsat
                    print "PASS - verified"
            # If they are the same user, the result should be sat
            elif u[0] == u[1]:
                if s.check() == sat:
                    # It shouldn't be sat
                    print "PASS - verified"
                else:
                    # It should be unsat
                    print "FAIL - unverified"
                    s.pop()
                    # Check why it's being unverified by checking seniority constraints
                    verify = self.verify_result_seniroity(original, s, u)
            s.pop()
            verify_original += "(pop)\n"
        print "bod verification check", s.check()
        return verify

    def verify_result_seniroity(self, original, s, u):
        print dict_seniority
        verify_user_list = users[:]
        verify_user_list.remove("bottom")
        verify = True
        if dict_seniority:
            for t_key, t_value in dict_eq_tasks.iteritems():
                verify_original = original[:]
                s.push()
                print "="
                # If they are listed as SoD then it shouldn't work as equality is BoD - they should be the same user
                verify_original += "(assert (= " + u[0] + " " + u[1] + "))"
                v = z3.parse_smt2_string(verify_original)
                s.add(v)
                if s.check() == unsat:
                    # They should be the same user - but it's not - so unsat
                    if u[0] == u[1]:
                        # If they are the same user but unsat - then false
                        verify = False
                else:
                    if u[0] != u[1]:
                        # If it is sat and they are different users - then false
                        verify = False
                s.pop()
            for t_key, t_value in dict_gt_tasks.iteritems():
                verify_original = original[:]
                print dict_gt_tasks
                print ">"
                print s.check()
                for v in t_value:
                    s.push()
                    print s.check()
                    verify_original += "(assert " \
                                       "(and " \
                                       "(executed " + t_key + ") " \
                                       "(= (alloc_user " + t_key +")" + u[0] + ")" \
                                       "(= (alloc_user " + v + ")" + u[1] + ")))"
                    v = z3.parse_smt2_string(verify_original)
                    s.add(v)
                    print "CHECKING"
                    print s.check()
                    if s.check() == unsat:
                        for u_key, u_value in dict_seniority.iteritems():
                            print "u_key", u_key
                            print "u_value", u_value
                            print "u[0]", u[0]
                            print "u[1]", u[1]
                            # If the input says that the user is more senior - then it shouldn't be unsat
                            if u[0] == u_key and u[1] in u_value:
                                verify = False
                            print verify
                    else:
                        # Check if they are actually senior in dict_seniority
                        # if not dict_seniority.has_key(u[0]):
                        #         verify = False
                        for u_key, u_value in dict_seniority.iteritems():
                            if u[0] == u_key and u[1] not in u_value:
                                verify = False
                        print verify
                    s.pop()
            for t_key, t_value in dict_lt_tasks.iteritems():
                print "<"
                for v in t_value:
                    verify_original = original[:]
                    s.push()
                    verify_original += "(assert " \
                                       "(and" \
                                       "(executed " + t_key + ") " \
                                       "(= (alloc_user " + t_key +")" + u[1] + ")" \
                                       "(= (alloc_user " + v + ")" + u[0] + ")))"
                    print "verify original", "(assert " \
                                       "(and" \
                                       "(executed " + t_key + ") " \
                                       "(= (alloc_user " + t_key +")" + u[1] + ")" \
                                       "(= (alloc_user " + v + ")" + u[0] + ")))"
                    v = z3.parse_smt2_string(verify_original)
                    s.add(v)
                    print s.check()
                    if s.check() == unsat:
                        for u_key, u_value in dict_seniority.iteritems():
                            print "u_key", u_key
                            print "u_value", u_value
                            print "u[0]", u[0]
                            print "u[1]", u[1]
                            # If the input says that the user is more senior - then it should be unsat
                            # If u[0] is actually senior to u[1], then it should be unsat
                            # If u[1] is actually senior to u[0], then it should be sat - so why is it in unsat
                            if u[0] == u_key and u[1] in u_value:
                                # If in fact they u[0] is more senior than u[1] then it should be false
                                verify = False
                            print verify
                    else:
                        # Check if they are actually senior in dict_seniority, if they are then it should be sat
                        # if u[1] in dict_seniority:
                        #     print "dict seniority has got key", u[1]
                        #     verify = False
                        for u_key, u_value in dict_seniority.iteritems():
                            if u[0] == u_key and u[1] not in u_value:
                                print "has u_key, doesn't have u_value"
                                verify = False
                        print verify
                    s.pop()
            for t_key, t_value in dict_neq_tasks.iteritems():
                verify_original = original[:]
                print "!="
                # If they are listed as SoD then it shouldn't work as equality is BoD - they should be the same user
                verify_original += "(assert (not(= " + u[0] + " " + u[1] + ")))"
                v = z3.parse_smt2_string(verify_original)
                s.add(v)
                if s.check() == unsat:
                    # They should be the same user - but it's not - so unsat
                    # But if it's unsat but they're actually different users then verify should be false
                    if u[0] != u[1]:
                        verify = False
                else:
                    #If it's sat and they are actually the same user - verify should be false
                    if u[0] == u[1]:
                        verify = False
                s.pop()
        return verify

    def evaluate_final_model(self, model):
        model_user_map = { }
        model_task_map = { }
        model_function_map = { }
        model_list = []
        model_result_map = { }
        Task = DeclareSort('Task')
        User = DeclareSort('User')
        for ms in model:
            if str(ms) in users:
                model_user_map[ms] = model[ms]
            if str(ms) in tasks:
                model_task_map[ms] = model[ms]
            if "before" in str(ms):
                model_function_map["before"] = model[ms]
                before_task_list = []
                for t in itertools.product(tasks, tasks):
                    t1 = Const(str(t[0]), Task)
                    t2 = Const(str(t[1]), Task)
                    before_tasks = model.eval(ms(t1, t2))
                    # TOD): Why does this let false???
                    if str(model.eval(ms(t1, t2))) == "True":
                        before_task_list.append(t)
                model_result_map["before"] = before_task_list
            if "alloc_user" in str(ms):
                model_function_map["alloc_user"] = model[ms]
                model_list_list = []
                for t_key, t_value in model_task_map.iteritems():
                    t = Const(str(t_key), Task)
                    user_solution = model.eval(ms(t))
                    for u_key, u_value in model_user_map.iteritems():
                        if str(u_value) == str(user_solution):
                            model_list_list.append((u_key, t_key))
                if model_list_list not in model_list:
                    model_list.append(model_list_list)
                    model_result_map["alloc_user"] = model_list
            if "executed" in str(ms):
                model_function_map["executed"] = model[ms]
                # List of executed tasks
                executed_task_list = []
                for t_key, t_value in model_task_map.iteritems():
                    t = Const(str(t_key), Task)
                    executed_task = model.eval(ms(t))
                    if executed_task:
                        executed_task_list.append(t_key)
                    model_result_map["executed_tasks"] = executed_task_list
            if "seniority" in str(ms) and "!" not in str(ms):
                model_function_map["seniority"] = model[ms]
                senior_users_list = []
                for u in itertools.product(users, users):
                    u1 = Const(str(u[0]), User)
                    u2 = Const(str(u[1]), User)
                    senior_users = model.eval(ms(u1, u2))
                    # TOD): Why does this let false???
                    if str(model.eval(ms(u1, u2))) == "True":
                        # print "senior_users"
                        # if (u[0], u[1]) not in senior_users_list:
                        # print "senior users", (u[0], u[1])
                        senior_users_list.append(u)
                model_result_map["seniority"] = senior_users_list
        print "model result map", model_result_map
        # print "model function map", model_function_map

    def prompt(self):
        return raw_input('busines_process > ')

if __name__ == '__main__':
    p = p_c()
    p.main(p.prompt())