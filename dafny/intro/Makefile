DAFNY_PATH=~/software/dafny/Dafny.exe
MONO_PATH=/usr/bin/mono

all: clean sum max2 max3 square sq swap mod16 add5

sum:
	$(MONO_PATH) $(DAFNY_PATH) sum.dfy

max2:
	$(MONO_PATH) $(DAFNY_PATH) max2.dfy

max3:
	$(MONO_PATH) $(DAFNY_PATH) max3.dfy

square:
	$(MONO_PATH) $(DAFNY_PATH) square.dfy

sq:
	$(MONO_PATH) $(DAFNY_PATH) sq.dfy

swap:
	$(MONO_PATH) $(DAFNY_PATH) swap.dfy

mod16:
	$(MONO_PATH) $(DAFNY_PATH) mod16counter.dfy

add5:
	$(MONO_PATH) $(DAFNY_PATH) add5.dfy

clean:
	rm -f *.dll *.mdb
