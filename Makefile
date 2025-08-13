# Project Makefile

.PHONY : bnfc clean all clean

all:
	$(MAKE) -C src all

clean :
	$(MAKE) -C src clean

bnfc :
	bnfc --haskell -d -m Stella.cf -o src

distclean :
	-rm -rf src/
