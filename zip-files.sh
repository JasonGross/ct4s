#!/bin/bash
coq_makefile *.v > Makefile
make html
zip jasonssubmissions.zip html/ html/* *.v index.html Makefile 2013*.pdf
