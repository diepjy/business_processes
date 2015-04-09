__author__ = 'joanna'

import ply.yacc as yacc
from Lexer import tokens

class parser_class(object):

    def __self__(self):
        self.rules_used = []
        self.tasks = []
        self.users = []
        self.before = []
        self.seniority = []
        self.sod = []
        # user pairs and task pairs should be indexes???

        self.smt_sort_task = "(declare-sort Task) \n"
        self.smt_sort_user = "(declare-sort User) \n"
        self.smt_fun_before = "(declare-fun before (Task Task) Bool) \n"
        self.smt_fun_seniority = "(declare-fun seniority (User User) Bool) \n"
        self.smt_fun_sod = "(declare-fun sod (Task) User) \n"
        self.smt_fun_bod = "(declare-fun bod (Task) User) \n"

    smt = ""

    # TODO: option flags

    def p_prog(self, p):
        '''prog : begin
                | begin rules'''

    def p_begin(self, p):
        '''begin : TASKS COLON task_node
                 | USERS COLON user_node'''
        global smt
        if p[1] not in self.rules_used and p[1] == 'Tasks':
            p[0] = p[3]
            self.rules_used.append(p[1])
            smt = self.smt_sort_task + smt
        elif p[1] not in self.rules_used and p[1] == 'Users':
            p[0] = p[3]
            smt = self.smt_sort_user + smt
        else:
            print "p error here"
            self.p_error(p)

    def p_rules(self, p):
        '''rules : BEFORE COLON task_node_pair
                 | SENIORITY COLON user_node_pair
                 | SOD COLON task_node_pair
                 | BOD COLON task_node_pair'''
        p[0] = p[3]

    def p_task_pair(self, p):
        '''task_node_pair : LPAREN NODE COMMA NODE RPAREN END
                     | LPAREN NODE COMMA NODE RPAREN COMMA task_node_pair'''
        if p[2] in self.tasks and p[4] in self.tasks:
            p[0] = [p[2]] + [p[4]]
            self.before.append(p[0])
        else:
            self.p_error(p)

    def p_user_pair(self, p):
        '''user_node_pair : LPAREN NODE COMMA NODE RPAREN END
                          | LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair'''
        if p[2] in self.users and p[4] in self.users:
            p[0] = [p[2]] + [p[4]]
            self.seniority.append(p[0])
        else:
            self.p_error(p)

    def p_task_node(self, p):
        '''task_node : NODE end
                | NODE COMMA task_node
                | NODE task_option'''
        p[0] = p[1]
        self.tasks.append(p[0])
        global smt
        smt = "(declare-const " + p[0] + " Tasks)\n" + smt

    def p_user_node(self, p):
        '''user_node : NODE end
                | NODE COMMA user_node
                | NODE user_option'''
        p[0] = p[1]
        self.users.append(p[0])
        global smt
        smt = "(declare-const " + p[0] + " Users) \n" + smt

    def p_task_option(p):
        '''task_option : OPTION task_option
                  | OPTION COMMA task_node
                  | OPTION end'''
        p[0] = p[1]

    def p_user_option(self, p):
        '''user_option : OPTION user_option
              | OPTION COMMA user_node
              | OPTION end'''
        p[0] = p[1]

    def p_end(self, p):
        '''end : END
               | END begin'''
        p[0] = p[1]

    def p_error(slelf, p):
        print "Syntax error in input!"