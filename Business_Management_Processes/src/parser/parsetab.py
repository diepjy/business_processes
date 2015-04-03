
# parsetab.py
# This file is automatically generated. Do not edit.
_tabversion = '3.2'

_lr_method = 'LALR'

_lr_signature = 'TRg\xe9\x9d\xae\xe0f\x9c\x13QF\xd1r\x0c\x8a'
    
_lr_action_items = {'NODE':([4,5,11,15,],[7,7,7,7,]),'OPTION':([7,12,],[12,12,]),'TASKS':([0,],[2,]),'END':([7,12,],[9,14,]),'USERS':([0,],[3,]),'COMMA':([7,12,],[11,15,]),'COLON':([2,3,],[4,5,]),'$end':([1,6,8,9,10,13,14,16,17,],[0,-1,-2,-4,-6,-5,-9,-7,-8,]),}

_lr_action = { }
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = { }
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'node':([4,5,11,15,],[6,8,13,17,]),'begin':([0,],[1,]),'option':([7,12,],[10,16,]),}

_lr_goto = { }
for _k, _v in _lr_goto_items.items():
   for _x,_y in zip(_v[0],_v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = { }
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> begin","S'",1,None,None,None),
  ('begin -> TASKS COLON node','begin',3,'p_begin','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',12),
  ('begin -> USERS COLON node','begin',3,'p_begin','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',13),
  ('begin_user -> <empty>','begin_user',0,'p_user','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',25),
  ('node -> NODE END','node',2,'p_task_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',33),
  ('node -> NODE COMMA node','node',3,'p_task_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',34),
  ('node -> NODE option','node',2,'p_task_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',35),
  ('option -> OPTION option','option',2,'p_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',39),
  ('option -> OPTION COMMA node','option',3,'p_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',40),
  ('option -> OPTION END','option',2,'p_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/Parser.py',41),
]