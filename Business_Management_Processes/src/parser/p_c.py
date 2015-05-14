__author__ = 'joanna'

from lexer_class import *

class p_c(object):

    tokens = lexer_class.tokens

    smt = ""

    smt_sort_task = "(declare-sort Task) \n"
    smt_sort_task = "(declare-sort Task) \n"
    smt_sort_user = "(declare-sort User) \n"
    smt_fun_before = "(declare-fun before (Task Task) Bool) \n"
    smt_fun_seniority = "(declare-fun seniority (User User) Bool) \n"
    smt_fun_executed = "(declare-fun executed (Task) Bool)\n"

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
    def __init__(self):
        self.rules_used = []
        self.tasks = []
        self.users = []
        self.dict_tasks = { }
        self.dict_users = { }
        self.dict_seniority = { }
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
        p_c.smt = p_c.smt.translate(None, '!@#$\'')

    def p_begin(self, p):
        '''begin : TASKS COLON task_node USERS COLON user_node
                 | TASKS COLON task_node USERS COLON user_node rules'''
        # p_c.smt = p_c.smt_before_transitivity + p_c.smt
        # p_c.smt = p_c.smt_fun_seniority_transitivity + p_c.smt
        # p_c.smt = p_c.smt_users_neq_bottom + p_c.smt
        # p_c.smt = p_c.smt_non_cyclic_before + p_c.smt
        # p_c.smt = p_c.smt_non_cyclic_seniority + p_c.smt
        self.users.append('bottom')
        # p_c.smt = p_c.smt_fun_executed + p_c.smt
        # p_c.smt = p_c.smt_fun_before + p_c.smt
        # p_c.smt = p_c.smt_fun_seniority + p_c.smt
        # p_c.smt = p_c.smt_const_bottom + p_c.smt
        # p_c.smt =  p_c.smt_fun_alloc_user + p_c.smt
        # p_c.smt = p_c.smt_sort_user + p_c.smt
        # p_c.smt = p_c.smt_sort_task + p_c.smt
        p[0] = p[3] + p[6]

    def p_rules(self, p):
        '''rules : BEFORE COLON before_task_node_pair
                 | BOD COLON bod_task_node_pair
                 | SOD COLON sod_task_node_pair
                 | SENIORITY COLON user_node_pair
                 | ALLOC COLON allocation_pair
                 | AUTHORISED COLON authorised_pair
                 | EXECUTION COLON fork
        '''
        p[0] = p[3]

    def p_before_task_pair(self, p):
        '''before_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA before_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        p_c.smt += "(assert (before " + p[2] + " " + p[4] + "))\n"
        p[0] = [p[2]] + [p[4]]

    def p_bod_task_pair(self, p):
        '''bod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA bod_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        p[0] = [p[2]] + [p[4]]
        p_c.smt += "(assert (= (alloc_user " + p[2] + ") (alloc_user " + p[4] + ")))\n"
        self.dict_bod.append([p[2].replace("'", "")] + [p[4].replace("'", "")])

    def p_sod_task_pair(self, p):
        '''sod_task_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                     | LPAREN NODE COMMA NODE RPAREN COMMA sod_task_node_pair
                     | LPAREN NODE COMMA NODE RPAREN END
                     '''
        p[0] = [p[2]] + [p[4]]
        p_c.smt += "(assert (not (= (alloc_user " + p[2] + ") (alloc_user " + p[4] + "))))\n"
        self.dict_sod.append([p[2].replace("'", "")] + [p[4].replace("'", "")])

    def p_user_pair(self, p):
        '''user_node_pair : LPAREN NODE COMMA NODE RPAREN END rules
                          | LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair
                          | LPAREN NODE COMMA NODE RPAREN END
                          '''
        p[0] = [p[2]] + [p[4]]
        p_c.smt += "(assert (seniority " + p[2] + " " + p[4] + ")) \n"

    # ie Alloc: ('u3', 't3')
    def p_allocation_pair(self, p):
        '''allocation_pair : LPAREN NODE COMMA NODE RPAREN END rules
                          | LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair
                          | LPAREN NODE COMMA NODE RPAREN END
        '''
        p[0] = [p[2]] + [p[4]]
        self.dict_user_alloc[p[2].replace("'", "")] = p[4].replace("'", "")
        p_c.smt += "(assert (=(alloc_user " + p[4] + ")" + p[2] + "))\n"

    def p_authorised_pair(self, p):
        '''authorised_pair : LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN END rules
                           | LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN COMMA authorised_pair
                           | LPAREN NODE COMMA LSQPAREN user_list RSQPAREN RPAREN END
        '''
        p[0] = [p[2]] + [p[5]]
        print p[5]
        self.dict_task_user_auth[p[2].replace("'", "")] = (p[5].replace("'", "")).split(",")
        print "dict_task_user_auth: ", self.dict_task_user_auth


    def p_user_list(self, p):
        '''user_list : NODE COMMA user_list
                     | NODE
        '''
        if len(p) == 2:
            p[0] = p[1]
        print len(p)
        if len(p) > 2:
            print p[3]
            p[0] = p[1] + p[2] + p[3]

    def p_task_node(self, p):
        '''task_node : NODE end
                | NODE COMMA task_node
                | NODE variable_task_option
                | NODE task_option'''
        p[0] = p[1]
        self.task = p[0]
        # if p[0] not in p_c.tasks:
        self.tasks.append(p[0].replace("'", ""))
        if len(p) == 3:
            self.dict_tasks[p[1].replace("'", "")] = p[2]

    def p_user_node(self, p):
        '''user_node : NODE end
                | NODE COMMA user_node
                | NODE user_option
                | NODE end_rule'''
        p[0] = p[1]
        if p[0] not in self.users:
            self.users.append(p[0].replace("'", ""))
        print "user nodes", self.users

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
        if "Or" in p[1]:
            self.dict_or_task[p[3].replace("'", "")] = (p[6].replace("'", "")).split(",")
            print "dict_task_or_task: ", self.dict_or_task
        if "Xor" in p[1]:
            self.dict_xor_task[p[3].replace("'", "")] = (p[6].replace("'", "")).split(",")
            print "dict_task_xor_task: ", self.dict_xor_task

    def p_task_list(self, p):
        '''task_list : NODE COMMA task_list
                     | NODE
        '''
        if len(p) == 2:
            p[0] = p[1]
        print len(p)
        if len(p) > 2:
            print p[3]
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
        else:
            self.p_error(p)

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