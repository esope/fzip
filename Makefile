OCB=ocamlbuild -use-ocamlfind -j 0
DOTFILE=_project.dot

bin:
	$(OCB) main.byte

native:
	$(OCB) main.native

test:
	$(OCB) -no-links test.byte --

test.native:
	$(OCB) -no-links test.native --

doc:
	$(OCB) project.docdir/index.html

view_doc:	doc
	xdg-open project.docdir/index.html

full_dot:	ocamldot bin
	ocamldep -I _build _build/*.ml _build/*.mli | _build/tools/ocamldot/ocamldot.byte -fullgraph > _build/$(DOTFILE)

dot:	ocamldot bin
	ocamldep -I _build _build/*.ml _build/*.mli | _build/tools/ocamldot/ocamldot.byte > _build/$(DOTFILE)

view_dot:	dot
	dot -T xlib _build/$(DOTFILE) &

view_full_dot:	full_dot
	dot -T xlib _build/$(DOTFILE) &

all:	bin doc dot

clean:
	$(OCB) -clean

distclean:	clean
	rm -rf *~
	rm -rf examples/*/*~

archive:
	hg archive --type tbz2 ../fzip.tar.bz2

ocamldot:
	$(OCB) tools/ocamldot/ocamldot.byte

.PHONY: bin native test test.native doc view_doc full_dot dot view_dot view_full_dot all clean distclean archive ocamldot
