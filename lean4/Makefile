
LEAN_ROOT := $(dir $(shell which lean))../

LFSC : LFSC.o
	leanc -o $@ $<

LFSC.o : LFSC.c
	leanc -o $@ -c -O3 $<

LFSC.c : LFSC.lean
	LEAN_PATH="Init=$(LEAN_ROOT)lib/lean/Init:LFSC=." lean --c=$@ --make $<

clean :
	rm LFSC LFSC.c

.PHONY : clean

LFSC.olean : LFSC.lean
	lean --make $<
