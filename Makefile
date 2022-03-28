all :
	ocamlc invariants.ml -o invariants

clean :
	rm -f *.cmi *.cmx *.o *.cmo invariants