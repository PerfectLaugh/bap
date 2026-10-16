.PHONY: doc


doc:
	../_build/default/tools/bapdoc.exe 2>bapdoc.log || \
	  { tail -n 20 bapdoc.log >&2; exit 1; }
