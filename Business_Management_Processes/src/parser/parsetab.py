
# parsetab.py
# This file is automatically generated. Do not edit.
_tabversion = '3.2'

_lr_method = 'LALR'

_lr_signature = '>\x97<6(s\xf2\xf0\xad[\xc8{\x7f[8g'
    
_lr_action_items = {'NODE':([4,9,16,17,18,19,20,29,34,56,58,59,62,69,70,71,72,],[5,5,22,24,25,26,27,5,22,65,66,67,68,73,74,75,76,]),'GEQ':([13,],[17,]),'TASKS':([0,10,36,],[2,2,2,]),'END':([5,21,22,24,25,26,27,32,54,77,78,79,80,],[10,10,36,-27,-28,-29,-26,10,64,82,84,86,88,]),'OPTION':([5,21,22,24,25,26,27,32,],[8,8,32,-27,-28,-29,-26,32,]),'NEQ':([13,],[19,]),'SOD':([10,15,23,31,33,35,36,37,43,44,45,47,48,53,55,57,60,61,63,64,82,84,86,88,89,90,91,92,],[-35,-36,38,-19,-22,-21,38,-3,-33,-30,-31,-20,-37,-32,-6,-7,-5,-4,-34,38,-12,-14,-10,-8,-13,-15,-11,-9,]),'USERS':([6,7,10,11,14,15,23,28,30,31,33,35,36,37,42,43,44,45,47,48,53,55,57,60,61,63,82,84,86,88,89,90,91,92,],[12,-16,-35,-18,-17,-36,-2,-25,-23,-19,-22,-21,-35,-3,-24,-33,-30,-31,-20,-37,-32,-6,-7,-5,-4,-34,-12,-14,-10,-8,-13,-15,-11,-9,]),'RPAREN':([73,74,75,76,],[77,78,79,80,]),'LEQ':([13,],[18,]),'COLON':([2,8,12,32,38,39,40,41,],[4,13,16,46,49,50,51,52,]),'ALLOCATE':([46,],[54,]),'LPAREN':([49,50,51,52,81,83,85,87,],[56,58,59,62,56,58,59,62,]),'SENIORITY':([10,15,23,31,33,35,36,37,43,44,45,47,48,53,55,57,60,61,63,64,82,84,86,88,89,90,91,92,],[-35,-36,39,-19,-22,-21,39,-3,-33,-30,-31,-20,-37,-32,-6,-7,-5,-4,-34,39,-12,-14,-10,-8,-13,-15,-11,-9,]),'COMMA':([5,21,22,24,25,26,27,32,65,66,67,68,77,78,79,80,],[9,29,34,-27,-28,-29,-26,45,69,70,71,72,81,83,85,87,]),'BEFORE':([10,15,23,31,33,35,36,37,43,44,45,47,48,53,55,57,60,61,63,64,82,84,86,88,89,90,91,92,],[-35,-36,41,-19,-22,-21,41,-3,-33,-30,-31,-20,-37,-32,-6,-7,-5,-4,-34,41,-12,-14,-10,-8,-13,-15,-11,-9,]),'BOD':([10,15,23,31,33,35,36,37,43,44,45,47,48,53,55,57,60,61,63,64,82,84,86,88,89,90,91,92,],[-35,-36,40,-19,-22,-21,40,-3,-33,-30,-31,-20,-37,-32,-6,-7,-5,-4,-34,40,-12,-14,-10,-8,-13,-15,-11,-9,]),'EQ':([13,],[20,]),'$end':([1,3,10,15,23,31,33,35,36,37,43,44,45,47,48,53,55,57,60,61,63,82,84,86,88,89,90,91,92,],[-1,0,-35,-36,-2,-19,-22,-21,-35,-3,-33,-30,-31,-20,-37,-32,-6,-7,-5,-4,-34,-12,-14,-10,-8,-13,-15,-11,-9,]),}

_lr_action = { }
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = { }
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'begin':([0,10,36,],[1,15,15,]),'end':([5,21,22,32,],[7,28,31,43,]),'task_node':([4,9,29,],[6,14,42,]),'rules':([23,36,64,],[37,48,48,]),'user_node':([16,34,],[23,47,]),'sod_task_node_pair':([49,81,],[55,89,]),'user_node_pair':([50,83,],[57,90,]),'end_rule':([22,54,],[33,63,]),'users_global_option':([46,],[53,]),'before_task_node_pair':([52,87,],[61,92,]),'user_option':([22,32,],[35,44,]),'prog':([0,],[3,]),'bod_task_node_pair':([51,85,],[60,91,]),'task_option':([5,21,],[11,30,]),'op':([13,],[21,]),}

_lr_goto = { }
for _k, _v in _lr_goto_items.items():
   for _x,_y in zip(_v[0],_v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = { }
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> prog","S'",1,None,None,None),
  ('prog -> begin','prog',1,'p_prog','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',51),
  ('begin -> TASKS COLON task_node USERS COLON user_node','begin',6,'p_begin','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',57),
  ('begin -> TASKS COLON task_node USERS COLON user_node rules','begin',7,'p_begin','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',58),
  ('rules -> BEFORE COLON before_task_node_pair','rules',3,'p_rules','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',84),
  ('rules -> BOD COLON bod_task_node_pair','rules',3,'p_rules','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',85),
  ('rules -> SOD COLON sod_task_node_pair','rules',3,'p_rules','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',86),
  ('rules -> SENIORITY COLON user_node_pair','rules',3,'p_rules','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',87),
  ('before_task_node_pair -> LPAREN NODE COMMA NODE RPAREN END','before_task_node_pair',6,'p_before_task_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',92),
  ('before_task_node_pair -> LPAREN NODE COMMA NODE RPAREN COMMA before_task_node_pair','before_task_node_pair',7,'p_before_task_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',93),
  ('bod_task_node_pair -> LPAREN NODE COMMA NODE RPAREN END','bod_task_node_pair',6,'p_bod_task_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',100),
  ('bod_task_node_pair -> LPAREN NODE COMMA NODE RPAREN COMMA bod_task_node_pair','bod_task_node_pair',7,'p_bod_task_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',101),
  ('sod_task_node_pair -> LPAREN NODE COMMA NODE RPAREN END','sod_task_node_pair',6,'p_sod_task_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',107),
  ('sod_task_node_pair -> LPAREN NODE COMMA NODE RPAREN COMMA sod_task_node_pair','sod_task_node_pair',7,'p_sod_task_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',108),
  ('user_node_pair -> LPAREN NODE COMMA NODE RPAREN END','user_node_pair',6,'p_user_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',114),
  ('user_node_pair -> LPAREN NODE COMMA NODE RPAREN COMMA user_node_pair','user_node_pair',7,'p_user_pair','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',115),
  ('task_node -> NODE end','task_node',2,'p_task_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',123),
  ('task_node -> NODE COMMA task_node','task_node',3,'p_task_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',124),
  ('task_node -> NODE task_option','task_node',2,'p_task_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',125),
  ('user_node -> NODE end','user_node',2,'p_user_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',137),
  ('user_node -> NODE COMMA user_node','user_node',3,'p_user_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',138),
  ('user_node -> NODE user_option','user_node',2,'p_user_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',139),
  ('user_node -> NODE end_rule','user_node',2,'p_user_node','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',140),
  ('task_option -> OPTION COLON op task_option','task_option',4,'p_task_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',147),
  ('task_option -> OPTION COLON op COMMA task_node','task_option',5,'p_task_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',148),
  ('task_option -> OPTION COLON op end','task_option',4,'p_task_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',149),
  ('op -> EQ NODE','op',2,'p_op','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',161),
  ('op -> GEQ NODE','op',2,'p_op','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',162),
  ('op -> LEQ NODE','op',2,'p_op','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',163),
  ('op -> NEQ NODE','op',2,'p_op','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',164),
  ('user_option -> OPTION user_option','user_option',2,'p_user_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',170),
  ('user_option -> OPTION COMMA','user_option',2,'p_user_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',171),
  ('user_option -> OPTION COLON users_global_option','user_option',3,'p_user_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',172),
  ('user_option -> OPTION end','user_option',2,'p_user_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',173),
  ('users_global_option -> ALLOCATE end_rule','users_global_option',2,'p_users_global_option','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',178),
  ('end -> END','end',1,'p_end','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',186),
  ('end -> END begin','end',2,'p_end','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',187),
  ('end_rule -> END rules','end_rule',2,'p_end_rule','/home/joanna/Third_Year/Individual_Project/Business_Management_Processes/src/parser/p_c.py',192),
]
