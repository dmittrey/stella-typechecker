# Project Makefile

.PHONY : bnfc clean

bnfc :
	bnfc -d -m Stella.cf -o src

clean :
	-rm -rf src/
