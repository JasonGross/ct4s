VS := $(shell ls *.v)

.PHONY: coq clean html zip

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

html:: Makefile.coq
	$(MAKE) -f Makefile.coq html
	python ./make-index.py

zip: html
	zip jasonssubmissions.zip html/ html/* *.v index.html Makefile 2013*.pdf
