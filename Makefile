all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq:
	rocq makefile -f _CoqProject -o Makefile.coq

autosubst:
	autosubst -f -s urocq -v ge813 -p ./theories/autosubst/Ast_preamble.v -o ./theories/autosubst/Ast.v ./theories/autosubst/Ast.sig

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean autosubst
