__author__ = 'joanna'

from bin.z3 import *

class p_c(object):
    smt = ""

    smt_sort_task = "(declare-sort Task) \n"
    smt_sort_task = "(declare-sort Task) \n"
    smt_sort_user = "(declare-sort User) \n"
    smt_fun_before = "(declare-fun before (Task Task) Bool) \n"
    smt_fun_seniority = "(declare-fun seniority (User User) Bool) \n"

    smt_fun_alloc = "(declare-fun alloc (User Task) Bool)\n"
    smt_fun_alloc_user = "(declare-fun alloc_user (Task) User) \n"

    smt_const_bottom = "(declare-const bottom User) \n"

    rules_used = []
    tasks = []
    users = []

    allocate_users = False

    # task = Sort('task')
    # user = Sort('user')

    def __init__(self):
        self.before = []
        self.seniority = []
        self.sod = []
        # user pairs and task pairs should be indexes???

    # TODO: option flags

    def p_prog(self, p):
        '''prog : begin
                | begin rules'''
        p_c.smt = p_c.smt.translate(None, '!@#$\'')

    def p_begin(self, p):
        '''begin : TASKS COLON task_node
                 | USERS COLON user_node'''
        if p[1] not in p_c.rules_used and p[1] == 'Tasks':
            p_c.smt = p_c.smt_sort_task + p_c.smt
            p_c.rules_used.append(p[1])
            p[0] = p[3]
            print p_c.rules_used
        elif p[1] not in p_c.rules_used and p[1] == 'Users':
            p_c.smt = "(push) \n" + "(assert (forall ((t Task)) (not (=(alloc_user t) bottom)))) \n"  + p_c.smt
            p_c.smt = "(push) \n" + "(assert (forall ((t Task)) (not (=(alloc_user t) bottom)))) \n"  + p_c.smt
            p_c.users.append('bottom');
            p_c.smt = p_c.smt_const_bottom + p_c.smt
            p_c.smt =  p_c.smt_fun_alloc_user + p_c.smt
            p_c.smt = p_c.smt_fun_alloc + p_c.smt
            p_c.smt = p_c.smt_sort_user + p_c.smt
            p_c.rules_used.append(p[1])
            p[0] = p[3]
        else:
            self.p_error(p)

    def p_rules(self, p):
        '''rules : BEFORE COLON before_task_node_pair
                 | BOD COLON bod_task_node_pair
                 | SOD COLON sod_task_node_pair
                 | SENIORITY COLON user_node_pair
        '''
        print p[1]
        p[0] = p[3]

    def p_before_task_pair(self, p):
        '''before_task_node_pair : LPAREN NODE COMMA NODE RPAREN END
                     | LPAREN NODE COMMA NODE RPAREN COMMA before_task_node_pair'''
        if p[2].replace("'", "") in p_c.tasks and p[4].replace("'", "") in p_c.tasks:
            p_c.smt += "(assert (not (= (alloc_user " + p[2] + ") (alloc_user " + p[4] + "))))\n"
            p[0] = [p[2]] + [p[4]]
            # self.before.append(p[0])

    def p_bod_task_pair(self, p):
        '''bod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END
                     | LPAREN NODE COMMA NODE RPAREN COMMA bod_task_node_pair'''
        print "bod****"
        # if p[2].replace("'", "") in p_c.tasks and p[4].replace("'", "") in p_c.tasks:
        p[0] = [p[2]] + [p[4]]
        p_c.smt += "(assert (= (alloc_user " + p[2] + ") (alloc_user " + p[4] + ")))\n"

    def p_sod_task_pair(self, p):
        '''sod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END
                     | LPAREN NODE COMMA NODE RPAREN COMMA sod_task_node_pair'''
        print "sod"
        print p[2]
        print p_c.tasks
        # if p[2].replace("'", "") in p_c.tasks and p[4].replace("'", "") in p_c.tasks:
        p[0] = [p[2]] + [p[4]]
        p_c.smt += "(assert (not (= (alloc_user " + p[2] + ") (alloc_user " + p[4] + "))))\n"

    def p_user_pair(self, p):
        '''user_node_pair : LPAREN NODE COMMA NODE RPAREN END
                          | LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair'''
        if p[2] in p_c.users and p[4] in p_c.users:
            p[0] = [p[2]] + [p[4]]
        else:
            self.p_error(p)

    def p_task_node(self, p):
        '''task_node : NODE end
                | NODE COMMA task_node
                | NODE task_option'''
        p[0] = p[1]
        if p[0] not in p_c.tasks:
            p_c.tasks.append(p[0].replace("'", ""))
            p_c.smt = "(declare-const " + p[0] + " Task)\n" + p_c.smt

    def p_user_node(self, p):
        '''user_node : NODE end
                | NODE COMMA user_node
                | NODE user_option
                | NODE end_rule'''
        p[0] = p[1]
        if p[0] not in p_c.users:
            p_c.users.append(p[0].replace("'", ""))
            p_c.smt = "(declare-const " + p[0] + " User) \n" + p_c.smt

    def p_task_option(self,p):
        '''task_option : OPTION task_option
                  | OPTION COMMA task_node
                  | OPTION end
                  '''
        p[0] = p[1]

    def p_user_option(self, p):
        '''user_option : OPTION user_option
              | OPTION COMMA
              | OPTION COLON users_global_option
              | OPTION end
              '''
        p[0] = p[1]

    def p_users_global_option(self, p):
        '''users_global_option : ALLOCATE end_rule'''
        p[0] = p[1]
        if p[0] == 'allocate':
            # go through each user and
            p_c.allocate_users = True
        else:
            self.p_error(p)

    def p_end(self, p):
        '''end : END
               | END prog
               '''
        p[0] = p[1]
        # if len(p) == 2:
            # p_c.tasks = []
            # p_c.users = []
            # p_c.rules_used = []
            # p_c.smt = ""
            # p_c.allocate_users = False

    def p_end_rule(self, p):
        '''end_rule : END
                    | END rules'''
        if len(p) == 0:
            p[0] = p[1]
        else:
            p[0] = p[1]

    def p_error(self, p):
        print "Syntax error in input!"