C = coqc
FLAGS = 

all: Lexicographic.vo

Lexicographic.vo: Lexicographic.v BasicLogic.vo Order.vo Sets.vo Functions.vo Ordinal.vo
	$(C) Lexicographic.v
Order.vo: Order.v Sets.vo Ordinal.vo
	$(C) Order.v
Sets.vo: Sets.v BasicLogic.vo
	$(C) Sets.v
BasicLogic.vo: BasicLogic.v
	$(C) BasicLogic.v
Functions.vo: Functions.v Sets.vo
	$(C) Functions.v
Ordinal.vo: Ordinal.v Sets.vo BasicLogic.vo
	$(C) Ordinal.v