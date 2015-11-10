all: Makefile.coq
	$(MAKE) -f Makefile.coq

install: all
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: Make
	$(COQBIN)/coq_makefile -f Make -o Makefile.coq
