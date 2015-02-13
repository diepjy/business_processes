class Coin:

	#constructor
	def __init__(self, isFalse):
		self.isFalse = isFalse

	#Destructor
	def __del__(self):
	  	class_name = self.__class__.__name__