__author__ = 'joanna'

from z3 import *
from lexer_class import *
from ply.lex import lex
from ply.yacc import yacc
import itertools

class p_c(object):
    tokens = lexer_class.tokens

    smt_sort_task = "(declare-sort Task) \n"
    smt_sort_task = "(declare-sort Task) \n"
    smt_sort_user = "(declare-sort User) \n"
    smt_fun_before = "(declare-fun before (Task Task) Bool) \n"
    smt_fun_seniority = "(declare-fun seniority (User User) Bool) \n"
    smt_fun_executed = "(declare-fun executed (Task) Bool)\n"
    smt_fun_time_needed = "(declare-fun time_needed (Task) Real)\n"

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
        self.dict_tasks = { }
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

    def p_prog(self, p):
        '''prog : begin
        '''
        global users
        global tasks
        global dict_tasks
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
        users = self.users
        tasks = self.tasks
        # list of options to a task
        dict_tasks = self.dict_tasks
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
        self.dict_before[p[2].replace("'", "")] = (p[4].replace("'", "")).split(",")
        print "before ",  self.dict_before
        p[0] = [p[2]] + [p[4]]

    def p_bod_task_pair(self, p):
        '''bod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA bod_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        p[0] = [p[2]] + [p[4]]
        self.dict_bod.append([p[2].replace("'", "")] + [p[4].replace("'", "")])

    def p_sod_task_pair(self, p):
        '''sod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA sod_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        p[0] = [p[2]] + [p[4]]
        self.dict_sod.append([p[2].replace("'", "")] + [p[4].replace("'", "")])

    def p_user_pair(self, p):
        '''user_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                          | LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair
                          | LPAREN NODE COMMA NODE RPAREN END
                          '''
        p[0] = [p[2]] + [p[4]]
        self.dict_seniority[p[2].replace("'", "")] = (p[4].replace("'", "")).split(",")

    def p_authorised_pair(self, p):
        '''authorised_pair : LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN END rules
                           | LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN COMMA authorised_pair
                           | LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN END
        '''
        p[0] = [p[2]] + [p[5]]
        self.dict_task_user_auth[p[2].replace("'", "")] = (p[5].replace("'", "")).split(",")

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
                | NODE task_option'''
        p[0] = p[1]
        p_c.task = p[0]
        # if p[0] not in p_c.tasks:
        self.tasks.append(p[0].replace("'", ""))
        if len(p) == 3 and p[2] != ";":
            self.dict_tasks[p[1].replace("'", "")] = p[2]

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
                  '''
        p[0] = p[2] + p[3] + p[4]
        if len(p) == 6:
            print "length is 6"
            p[0] = p[2] + p[3] + p[4] + p[5]

    def p_task_option(self, p):
        '''task_option : OPTION option_flag task_option
                  | OPTION option_flag COMMA task_node
                  | OPTION option_flag end
                  '''
        p[0] = p[2]

    # ie -min_sec_lv:'t4'
    def p_variable_option_flag(self, p):
        '''variable_option_flag : MIN_SEC_LV
        '''
        p[0] = p[1]

    # ie -start
    def p_option_flag(self, p):
        '''option_flag : START
        '''
        p[0] = p[1]

    def p_op(self, p):
        '''op : EQ NODE
              | GEQ NODE
              | LEQ NODE
              | NEQ NODE
              '''
        p[0] = p[1] + p[2]

    def p_execution(self, p):
        '''fork : OR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END rules
                | OR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN COMMA fork
                | OR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END
                | XOR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END rules
                | XOR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN COMMA fork
                | XOR LPAREN NODE COMMA LSQPAREN task_list RSQPAREN RPAREN END
        '''
        p[0] = [p[3]] + [p[6]]
        print p[1]
        if p[1] == "Or":
            print "in or"
            self.dict_or_task[p[3].replace("'", "")] = (p[6].replace("'", "")).split(",")
        elif p[1] == "Xor":
            print "in xor"
            self.dict_xor_task[p[3].replace("'", "")] = (p[6].replace("'", "")).split(",")

    def p_task_list(self, p):
        '''task_list : NODE COMMA task_list
                     | NODE
        '''
        if len(p) == 2:
            p[0] = p[1]
        print len(p)
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

    def get_task_options(self, d, task_list):
        smt_options = ""
        for key, value in d.iteritems():
            if "min_sec_lv" in value:
                if "=" in value and "!=" not in value:
                    # BOD
                    print "= seniority"
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
                elif ">" in value:
                    # More senior allocation
                    print ">>>>>>> seniority"
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
                                           ")"
                elif "<" in value:
                    print "<<<<<<< seniority"
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
                                           ")"
                elif "!=" in value:
                    # SOD
                    print "!!!!!!! seniority"
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
            p_c.smt_fun_time_needed + \
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
            a = z3.parse_smt2_string(original)
            s.add(a)
            print "Result of before and seniority", s.check()
            s.model()

            try:
                # go through the options and check if they are possible given the basic model
                smt_options = self.get_task_options(dict_tasks, tasks)
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

        print "ASSIGNMENT"
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
                    print "tasks", str(model_task[0])
                    user_solution = m.eval(ms(t))
                    for model_user in model_map_user:
                        if str(model_user[1]) == str(user_solution):
                            print "model user", str(model_user[0])
                            solution_map.append((t, model_user[0]))
                    print user_solution
        print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
        print s.check()
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
                    #Need to check other cases to see why it doesn't satisfy
                    print "UNVERIFIED BOD"
                verify_seniroity = self.verify_result_seniroity(original, s, u)
                if verify_seniroity:
                    print "VERIFIED SENIORITY"
                else:
                    print "UNVERIFIED SENIORITY"
                print "================================================================"

                # elif dict_bod and not dict_sod:
                #     verify_bod = self.verify_result_bod(s.model(), original, s, u)
                #     if verify_bod:
                #         # Don't need to do anything
                #         print "VERFIFIED BOD"
                #     else:
                #         #Need to check other cases to see why it doesn't satisfy
                #         print "UNVERIFIED BOD"
                #         verify_seniroity = self.verify_result_seniroity(s.model(), original, s, u)
                #         if verify_seniroity:
                #             print "VERIFIED SENIORITY"
                #         else:
                #             print "UNVERIFIED SENIORITY"
                # elif dict_seniority and not dict_sod and not dict_bod:
                #     verify_seniroity = self.verify_result_seniroity(s.model(), original, s, u)
                #     if verify_seniroity:
                #         print "VERIFIED SENIORITY"
                #     else:
                #         print "UNVERIFIED SENIORITY"
        if not solution_map:
            return str(s.check())
        else:
            return str(s.check()) + " " + str(solution_map).strip('[]')

    # Pass the model and check that it is consistent with the input
    # Sod verification: if it's the same user, should return unsat
    def verify_result_sod(self, original, s, u):
        # for sod in dict_sod:
        # Task = DeclareSort('Task')
        # print model
        # for ms in model:
        #     print ms
        #     t = Const("t3", Task)
        #     if str(ms) == "alloc_user":
        #         print "eval t3", model.eval(ms(t))
        #         print "delarations is", model.decls()
            # If they are the same user, the result should be unsat
        verify_user_list = users[:]
        verify_user_list.remove("bottom")
        verify_original = original[:]
        verify = True
        s.push()
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
                    print "FAIL - unverified"
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
                    # It shouldn't be sat
                    print "PASS - verified"
                    s.pop()
                    verify_original += "(pop)\n"
                else:
                    # It should be unsat
                    print "FAIL - unverified"
                    verify = False
                    s.pop()
                    verify_original += "(pop)\n"
        print "sod check verification", s.check()
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
            print "check before add", s.check()
            print u
            s.push()
            verify_original += "(push)\n"
            verify_original += "(assert (and (executed " + bod[0] +") (= (alloc_user " + bod[0] +")" + u[0] + ")))\n"
            verify_original += "(assert (and (executed " + bod[1] +") (= (alloc_user " + bod[1] +")" + u[1] + ")))\n"
            v = z3.parse_smt2_string(verify_original)
            s.add(v)
            # If they are different users, the result should be unsat
            if u[0] != u[1]:
                print "equal"
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
                    verify = False
            print "pop!!!"
            s.pop()
            verify_original += "(pop)\n"
        print "bod verification check", s.check()
        return verify

    def verify_result_seniroity(self, original, s, u):
        verify_user_list = users[:]
        verify_user_list.remove("bottom")
        verify_original = original[:]
        verify = True
        s.push()
        for t_key, t_value in dict_tasks.iteritems():
            if "=" in t_value and "!=" not in t_value:
                print "="
                # If they are listed as SoD then it shouldn't work as equality is BoD - they should be the same user
                verify_original += "(assert (= " + u[0] + " " + u[1] + "))"
                v = z3.parse_smt2_string(verify_original)
                s.add(v)
                if s.check() == unsat:
                    # They should be the same user - but it's not - so unsat
                    verify = False
                else:
                    verify = True
            elif ">" in t_value:
                print ">"
                s.push()
                verify_original += "(push)\n"
                verify_original += "(assert " \
                                   "(and (seniority " + u[0] + " " + u[1] + ") " \
                                   "(executed " + t_key + ") " \
                                   "(= (alloc_user " + t_key +")" + u[0] + ")))"
                v = z3.parse_smt2_string(verify_original)
                s.add(v)
                print "CHECKING"
                if s.check() == unsat:
                    print "UNSAT"
                    for u_key, u_value in dict_seniority.iteritems():
                        print "u_key", u_key
                        print "u[0]", u[0]
                        print "u[1]", u[1]
                        print dict_seniority
                        # If the input says that the user is more senior - then it should be unsat
                        if u[0] == u_key and u[1] in u_value:
                            verify = False
                else:
                    # Check if they are actually senior in dict_seniority
                    print "verify is true"
                    verify = True
                s.pop()
            elif "<" in t_value:
                print "<"
                verify_original += "(assert " \
                                   "(and (seniority " + u[0] + " " + u[1] + ") " \
                                   "(executed " + t_key + ") " \
                                   "(= (alloc_user " + t_key +")" + u[0] + ")))"
                v = z3.parse_smt2_string(verify_original)
                s.add(v)
                print "CHECKING"
                if s.check() == unsat:
                    for u_key, u_value in dict_seniority.iteritems():
                        print "u_key", u_key
                        print "u[0]", u[0]
                        print "u[1]", u[1]
                        print dict_seniority
                        # If the input says that the user is more senior - then it should be unsat
                        if u[0] == u_key and u[1] in u_value:
                            verify = False
                else:
                    verify = True
            elif "!=" in t_value:
                print "!="
                # If they are listed as SoD then it shouldn't work as equality is BoD - they should be the same user
                verify_original += "(assert (= " + u[0] + " " + u[1] + "))"
                v = z3.parse_smt2_string(verify_original)
                s.add(v)
                if s.check() == unsat:
                    # They should be the same user - but it's not - so unsat
                    verify = False
                else:
                    verify = True
        return verify

    def prompt(self):
        return raw_input('busines_process > ')

if __name__ == '__main__':
    p = p_c()
    p.main(p.prompt())